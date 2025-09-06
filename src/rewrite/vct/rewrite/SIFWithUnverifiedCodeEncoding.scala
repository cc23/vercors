package vct.rewrite

import com.typesafe.scalalogging.LazyLogging
import hre.util.ScopedStack
import vct.col.ast.{InstanceField, _}
import vct.col.origin.Name.Preferred
import vct.col.origin._
import vct.col.ref.Ref
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.util.AstBuildHelpers.tt
import vct.col.util.{PredicateExpSubstitute, Substitute}
import vct.result.VerificationError.SystemError
import vct.rewrite.HiddenLeakableToPredicates.{hiddenPredName, leakablePredName}
import vct.rewrite.SIFWithUnverifiedCodeEncoding.{
  indirectlyFromUcGhostParamName,
  indirectlyFromUcSeqName,
}

case object SIFWithUnverifiedCodeEncoding extends RewriterBuilder {
  val indirectlyFromUcGhostParamName: String = "indirectlyFromUc"
  val indirectlyFromUcSeqName: Seq[String] = Seq("indirectly", "from", "uc")

  override def key: String = "unverifiedCodeSIF"
  override def desc: String =
    "Resolve the leak operation for partially verified code."
}

case class SIFUCUnsupportedNode(node: Node[_]) extends SystemError {
  override def text: String =
    node.o.messageInContext("Node not supported in SIF UC Encoding")
}

case class SIFUCUnsupported(node: Node[_], message : String) extends SystemError {
  override def text: String =
    node.o.messageInContext(message)
}

case class SecondMethodVerificationFailed(app: InstanceMethod[_])
  extends Blame[CallableFailure] {

  override def blame(error: CallableFailure): Unit = {
    error match {
      case p: PostconditionFailed => app.blame.blame(SecondVerificationPostFailed(app, p.failure))
      case _ => app.blame.blame(error)
    }
  }
}

case class SecondConstructorVerificationFailed(app: Constructor[_])
  extends Blame[CallableFailure] {

  override def blame(error: CallableFailure): Unit = {
    error match {
      case p: PostconditionFailed => app.blame.blame(SecondVerificationPostFailed(app, p.failure))
      case _ => app.blame.blame(error)
    }
  }
}

case class SIFWithUnverifiedCodeEncoding[Pre <: Generation]() extends Rewriter[Pre] with LazyLogging {

  private class ArgSubstitute (oldArgs: Seq[Variable[Pre]], oldOutArgs : Seq[Variable[Pre]], oldTypeArgs : Seq[Variable[Pre]])  {
    val newArgs : Seq[Variable[Pre]] = oldArgs.map(declareNewVar[Pre])
    val newOutArgs: Seq[Variable[Pre]] = oldOutArgs.map(declareNewVar[Pre])
    // TypeArgs do not seem to be supported by VerCors currently
    val newTypeArgs: Seq[Variable[Pre]] = oldTypeArgs.map(declareNewVar[Pre])

    private val expSubs: Map[Expr[Pre], Expr[Pre]] = ((oldArgs ++ oldOutArgs).map[Expr[Pre]](a => Local[Pre](a.ref)(a.o))
      zip
      (newArgs ++ newOutArgs).map[Expr[Pre]](a => Local[Pre](a.ref)(a.o))
      ).toMap

    private val typeSubs: Map[TVar[Pre], Type[Pre]] = (oldTypeArgs.map[TVar[Pre]](a => TVar(a.ref))
      zip
      newTypeArgs.map[Type[Pre]](a => TVar(a.ref))
      ).toMap

    private val sub = Substitute(subs = expSubs, typeSubs = typeSubs)

    def dispatch(stat : Statement[Pre]) : Statement[Pre] = sub.dispatch(stat)

    def dispatch(sig : SignalsClause[Pre]) : SignalsClause[Pre] = sub.dispatch(sig)

    def dispatch(t : Type[Pre]) : Type[Pre] = sub.dispatch(t)
  }

  private def isIndirectlyFromUcGhostParam(arg : Variable[_]) : Boolean =
    arg.o.getPreferredName.get.camel == indirectlyFromUcGhostParamName

  private def noPrimitiveType(t: Type[Pre]): Boolean = t match {
    case clz: TByReferenceClass[_] => !isPrimitiveClass(clz)
    case _ => !t.isInstanceOf[PrimitiveType[Pre]]
  }

  private def isPrimitiveClass(clz: TByReferenceClass[Pre]) = {
    clz.cls.decl.o.getPreferredName.get.camel.contains("string")
  }

  private def setIndirectlyFromUC(args: Seq[Variable[Pre]], values: Seq[Expr[Pre]]) : Seq[Expr[Post]] = {
    val ghostParamIndex = args.indexWhere(isIndirectlyFromUcGhostParam)
    val ghostParamValue: Expr[Post] = if (isCurrentMethod2ndVerification.top) tt
    else Local(currentIndirectlyFromUcParam.top.ref[Variable[Post]])(origin(indirectlyFromUcSeqName))
    if(ghostParamIndex < 0){
      values.map(dispatch) :+ ghostParamValue
    } else {
      values.map(dispatch).updated(ghostParamIndex, ghostParamValue)
    }
  }

  private def inhaleNullFieldsLeakableHidden(clsPre: ByReferenceClass[Pre], fieldAccess: InstanceField[Pre] => Expr[Post])(implicit o : Origin)
  : Seq[Statement[Post]] = {
    clsPre.decls.collect { case field: InstanceField[_] => field }
      .filter(f => noPrimitiveType(f.t))
      .map[Statement[Post]](f => Branch(Seq(Eq(fieldAccess(f), Null()) ->
        Block(Seq(
        Inhale(leakable(fieldAccess(f))),
          Inhale(hiddenWrite(fieldAccess(f)))
        )))))
  }

  private def encodeLeak(objPre: Expr[Pre], blameWithMsg: String => Blame[VerificationFailure])(implicit o: Origin): Statement[Post] = {
    val obj = dispatch(objPre)
    val cls: ByReferenceClass[Pre] = getClsFromType(objPre.t)
    val inv: Expr[Post] = dispatch(
      Substitute(Map[Expr[Pre], Expr[Pre]](ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]) -> objPre))
        .dispatch(cls.ucInvariant)
    )
    Block(Seq[Statement[Post]](
      Assert(
        Or(Greater(curPermLeakable(obj), IntegerValue(0)),
          Greater(curPermHidden(obj), IntegerValue(0)))
      )(blameWithMsg(s"$obj should either be leakable or hidden")),
      Branch(Seq((Eq(curPermLeakable(obj), IntegerValue(0)),
        Block(Seq[Statement[Post]](
          Exhale(hiddenWrite(obj))(blameWithMsg(s"Might not have write perm to hidden($obj) during leak")),
          Inhale(leakable(obj)),
          Exhale(inv)(blameWithMsg(s"failed during exhaling inv: $inv")),
          Assert(LowEvent())(blameWithMsg("leak might not be lowEvent")),
          Assert(Low(obj))(blameWithMsg(s"$obj might not be low")),
        )
          ++
          getAllModifiableFields(cls)
            .map[Statement[Post]](f => Exhale(Perm(FieldLocation[Post](obj, succ(f)), WritePerm()))
            (blameWithMsg(s"missing write perm for field: $f")))
          ++
          getAllNonPrivateFields(cls)
            .map(f => {
              val fDeref = Deref[Post](obj, succ(f))(blameWithMsg(s"missing perm to read field $f"))
              Block(
                Assert(Low(fDeref))(blameWithMsg(s"field might not be low: $f"))
                  +:
                  (if(noPrimitiveType(f.t)) Seq(Assert(leakable(fDeref))(blameWithMsg(s"field might not be leakable: $f")))
                  else Seq())
                  :+
                  Exhale(Perm(FieldLocation[Post](obj, succ(f)), WritePerm()))(blameWithMsg(s"missing write perm for field: $f"))
              )
            })
        ))
      )
      )))
  }

  private def getAllModifiableFields[G](cls : ByReferenceClass[G]): Seq[InstanceField[G]] = {
    cls.decls.collect { case field: InstanceField[_] => field }
      .filter(_.flags.collect { case p : Private[_] => p}.nonEmpty)
      .filter(_.flags.collect { case p : Modifiable[_] => p}.nonEmpty)
  }

  private def getAllNonPrivateFields[G](cls : ByReferenceClass[G]): Seq[InstanceField[G]] = {
    cls.decls.collect { case field: InstanceField[_] => field }
      .filter(_.flags.collect { case p : Private[_] => p}.isEmpty)
  }


  private def noop(implicit o: Origin): Statement[Post] = Block[Post](Seq())

  private def hiddenRead(obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    Value(PredicateLocation(PredicateApply(hiddenPredRef, Seq(obj))))

  private def hiddenWrite(obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    Perm(
      PredicateLocation(PredicateApply(hiddenPredRef, Seq(obj))),
      WritePerm(),
    )

  private def leakable(obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    // leakable read and write permissions can be used interchangeably
    Value(PredicateLocation(PredicateApply(leakablePredRef, Seq(obj))))

  private def curPermHidden(obj: Expr[Post])(implicit o:Origin): Expr[Post] =
    CurPerm(PredicateLocation(PredicateApply(hiddenPredRef, Seq(obj))))

  private def curPermLeakable(obj: Expr[Post])(implicit o:Origin): Expr[Post] =
    CurPerm(PredicateLocation(PredicateApply(leakablePredRef, Seq(obj))))

  private def inhaleAllLowAndLeakable(variablesPre: Seq[Variable[Pre]], variablesPost: Seq[Variable[Post]])(implicit o : Origin) : Seq[Statement[Post]] = {
    val variables: Seq[(Variable[Pre], Variable[Post])] = variablesPre zip variablesPost
    variables.filter(arg => noPrimitiveType(arg._1.t))
      .map {
        case (_, vPost) => Inhale(leakable(Local(vPost.ref[Variable[Post]])))
      } ++
      variablesPost.map(arg => Assume(Low(Local(arg.ref[Variable[Post]]))))
  }

  private def declareNewVar[G](arg: Variable[G]): Variable[G] = {
    new Variable(arg.t)(origin(
      arg.o.getPreferredNameOrElse(Seq("unknown_var"))
    ))
  }

  private def declareNewVar[G](field: InstanceField[G]): Variable[G] = {
    new Variable(field.t)(origin(
      field.o.getPreferredNameOrElse(Seq("unknown_var"))
    ))
  }

  private def declareNewVar[G](field: InstanceField[G], nameAppend: String): Variable[G] = {
    new Variable(field.t)(origin(
      Preferred(Seq(field.o.getPreferredNameOrElse(Seq("unknown")).snake, nameAppend))
    ))
  }

  private def ifLeakableElse(conditionVariable: Expr[Post], ifBody: Statement[Post], elseBody: Statement[Post])(implicit o:Origin) : Statement[Post] =
    Branch(Seq(
      (Greater(curPermLeakable(conditionVariable), IntegerValue(0)), ifBody),
      (tt, elseBody)
    ))

  private def ifLeakable(conditionVariable: Expr[Post], ifBody: Statement[Post])(implicit o:Origin) : Statement[Post] =
    Branch(Seq((Greater(curPermLeakable(conditionVariable), IntegerValue(0)), ifBody)))

  private def ifLowEventLowRecvElse(receiver: Local[Post], ifBody: Statement[Post], elseBody: Statement[Post])(implicit o:Origin) : Statement[Post] =
    Branch(Seq(
      (And(LowEvent(), Low(receiver)), ifBody),
      (tt, elseBody)
    ))

  private def emptyAccountedPredicate(implicit o:Origin) : AccountedPredicate[Post] = getAccountedPredicate(Seq(tt[Post]))

  private def getAccountedPredicate(exp: Seq[Expr[Post]])(implicit o: Origin): AccountedPredicate[Post] =
    exp match {
      case Nil => emptyAccountedPredicate(o)
      case Seq(last) => UnitAccountedPredicate(last)
      case head +: tail =>
        SplitAccountedPredicate(
          UnitAccountedPredicate(head),
          getAccountedPredicate(tail),
        )
    }

  private def origin(preferredName: String): Origin =
    Origin(
      Seq(PreferredName(Seq(preferredName)), LabelContext("unverifiedCodeSIF"))
    )

  private def origin(preferredName: Seq[String]): Origin =
    Origin(
      Seq(PreferredName(preferredName), LabelContext("unverifiedCodeSIF"))
    )

  private def origin(preferredName: Name): Origin =
    Origin(Seq(IndirectName(preferredName), LabelContext("unverifiedCodeSIF")))

  var hiddenPredRef: Ref[Post, Predicate[Post]] = null
  var leakablePredRef: Ref[Post, Predicate[Post]] = null

  val currentClass: ScopedStack[ByReferenceClass[Pre]] = ScopedStack()
  val isCurrentMethod2ndVerification: ScopedStack[Boolean] = ScopedStack()
  val currentIndirectlyFromUcParam: ScopedStack[Variable[Post]] = ScopedStack()

  override def dispatch(expr: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = expr.o
    expr match { case other => other.rewriteDefault() }
  }

  override def dispatch(stat: Statement[Pre]): Statement[Post] = {
    implicit val o: Origin = stat.o
    stat match {
      case invCons : InvokeConstructor[_] =>
        val insideClass: ByReferenceClass[Pre] = currentClass.top
        if(invCons.outArgs.nonEmpty){
          throw SIFUCUnsupported(invCons, "ConstructorInvocations with outArgs not supported.")
        }
        val res: Local[Post] = dispatch(invCons.out) match {
          case l : Local[_] => l
          case other => throw SIFUCUnsupported(invCons, s"Result variable of ConstructorInvocation should be Local and not ${other.getClass}.")
        }
        val cls = invCons.cls match {
          case clazz: ByReferenceClass[_] => clazz
          case _ => throw SIFUCUnsupported(invCons, "Only supports ConstructorInvocations of ByReferenceClasses.")
        }
        val args: Seq[Expr[Post]] = invCons.args.map(dispatch)
          //skip first argument = tid
          .tail
        val newInv = invCons.rewrite(
          args = if (isClsFromLib(cls)) invCons.args.map(dispatch)
                  else setIndirectlyFromUC(invCons.ref.decl.args, invCons.args)
        )
        if(cls.isUnverified){
          Block(
            args.map { arg =>
              Assert(Low(arg))(err => invCons.blame.blame(InvocationSIFUCFailure(invCons, err.failure)))(arg.o)
            }
              ++
              (invCons.args zip args).filter(arg => noPrimitiveType(arg._1.t))
                .map(arg => arg._2)
              .map{arg => Assert(leakable(arg))(err => invCons.blame.blame(InvocationSIFUCFailure(invCons, err.failure)))(arg.o)}
              ++
            Seq[Statement[Post]](
              Assert(LowEvent())(_ => invCons.blame.blame(InvocationMustBeLowEvent(invCons))),
              newInv,
              Assume(Not(Eq(res, ThisObject[Post](succ(insideClass)))))(invCons.o), // see unverifiedcode/NewObjNotEqToThis.java
              Assume(Low(res))(invCons.o),
              Inhale(leakable(res)),
          ))
        } else {
          Block(Seq(
            Assert(LowEvent())(_ => invCons.blame.blame(InvocationMustBeLowEvent(invCons))),
            newInv,
            Assume(Not(Eq(res, ThisObject[Post](succ(insideClass)))))(invCons.o), // see unverifiedcode/NewObjNotEqToThis.java
          ))
        }
      case mInv : InvokeMethod[_] =>
        //TODO track RuntimeClass
        val cls: ByReferenceClass[Pre] = getClsFromType(mInv.obj.t)
        val newInv = mInv.rewrite(
          args = if (isClsFromLib(cls)) mInv.args.map(dispatch)
                  else setIndirectlyFromUC(mInv.ref.decl.args, mInv.args)
        )
        if (cls.isUnverified) {
          if (mInv.outArgs.size > 1) {
            throw SIFUCUnsupported(mInv, "Too many outArgs for MethodInvocation.")
          }
          val res: Local[Post] = dispatch(mInv.outArgs.head) match {
            case l: Local[_] => l
            case other => throw SIFUCUnsupported(mInv, s"Result variable of MethodInvocation should be Local and not ${other.getClass}.")
          }
          val args: Seq[Expr[Post]] = mInv.args.tail.map(dispatch) //skip first argument = tid
          Block(
            args.map { arg =>
              Assert(Low(arg))(err => mInv.blame.blame(InvocationSIFUCFailure(mInv, err.failure)))(arg.o)
            }
              ++
              (mInv.args zip args).filter(arg => noPrimitiveType(arg._1.t))
                .map(arg => arg._2)
                .map { arg => Assert(leakable(arg))(err => mInv.blame.blame(InvocationSIFUCFailure(mInv, err.failure)))(arg.o) }
              ++
              Seq[Statement[Post]](
                Assert(LowEvent())(_ => mInv.blame.blame(InvocationMustBeLowEvent(mInv))),
                Assert(Low(dispatch(mInv.obj)))(err => mInv.blame.blame(InvocationSIFUCFailure(mInv, err.failure)))(mInv.obj.o),
                newInv,
                Assume(Low(res))
              )
              ++ (if (noPrimitiveType(mInv.outArgs.head.t)) Seq(Inhale(leakable(res))) else Seq())
          )
        } else {
          newInv
        }
      // Field reads
      case assign @ Assign(resVar @ Local(_), Deref(receiver, fieldRef)) =>
        if(!(receiver.isInstanceOf[Local[Pre]] || receiver.isInstanceOf[ThisObject[Pre]])){
          logger.warn(s"receiver of unexpected type: $receiver")
        }
        val y: Local[Post]  = dispatch(resVar).asInstanceOf[Local[Post]]
        val x: Expr[Post] = dispatch(receiver)
        // here the static type is desirable
        val cls: ByReferenceClass[Pre] = getClsFromType(receiver.t)
        val isPrivate = fieldRef.decl.flags.exists{
          case Private() => true
          case _ => false
        }
        val isModifiable = fieldRef.decl.flags.exists{
          case Modifiable() => true
          case _ => false
        }
        if(isPrivate){
          val modFields: Seq[InstanceField[Pre]] = getAllModifiableFields(cls)
          val modVars = modFields.map(declareNewVar[Pre])
          val modVarsPost: Seq[Variable[Post]] = modVars.map(variables.dispatch)
          val modFieldSub = Substitute(
              (modFields
              .map(f =>
                Deref(ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]), f.ref.asInstanceOf[Ref[Pre, InstanceField[Pre]]])(PanicBlame("sub node")))
                zip
                modVars.map(v => Local[Pre](v.ref)))
              .toMap[Expr[Pre], Expr[Pre]]
              +
                (ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]) -> receiver)
          )
          val inv = modFieldSub.dispatch(cls.ucInvariant)
          val (unaryInv, relInv) = splitExprUnaryRel(inv)
          if(isModifiable){
            Block(Seq(
              Assert(
                Or(Greater(curPermLeakable(x), IntegerValue(0)),
                  Greater(curPermHidden(x), IntegerValue(0)))
              )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
              ifLeakableElse(x,
                ifBody = Scope(modVarsPost, Block(Seq[Statement[Post]](
                  Inhale(dispatch(unaryInv)),
                  Inhale(Implies(Low(x), dispatch(relInv))),
                  Assign(y, Local[Post](modVarsPost(modFields.indexOf(fieldRef.decl)).ref))(PanicBlame("assign local <- local should never fail")),
                ))),
                elseBody = assign.rewriteDefault())
            ))
          } else {
            Block(Seq(
              Assert(
                Or(Greater(curPermLeakable(x), IntegerValue(0)),
                  Greater(curPermHidden(x), IntegerValue(0)))
              )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
              ifLeakable(x,
                ifBody = Scope(modVarsPost, Block(Seq[Statement[Post]](
                  Inhale(dispatch(unaryInv)),
                  Inhale(Implies(Low(x), dispatch(relInv))),
                )))),
              assign.rewriteDefault(),
            ))
          }
        } else {
          if (isModifiable) {
            logger.warn(s"Field $fieldRef is public, no need to annotate it with 'modifiable'.")
          }
          // public / protected / package-private
          val tempVar: Variable[Post] = variables.dispatch(declareNewVar[Pre](fieldRef.decl))
          val temp: Local[Post] = Local(tempVar.ref)
          Block(Seq(
            Assert(
              Or(Greater(curPermLeakable(x), IntegerValue(0)),
                Greater(curPermHidden(x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(x,
              ifBody = Scope(Seq(tempVar), Block(
                (if(noPrimitiveType(fieldRef.decl.t)) Seq(Inhale(leakable(temp))) else Seq())
                ++
                Seq[Statement[Post]](
                Assume(Implies(Low(x), Low(temp))),
                Assign(y, temp)(PanicBlame("assign local <- local should never fail")),
              ))),
              elseBody = assign.rewriteDefault())
          ))
        }
      case l @ Leak(objPre) => encodeLeak(objPre, msg => err => l.blame.blame(LeakFailed(l, msg)))
      //Field writes
      case assign @ Assign(Deref(receiver, fieldRef), newVal) =>
        if(!(receiver.isInstanceOf[Local[Pre]] || receiver.isInstanceOf[ThisObject[Pre]])){
          logger.warn(s"receiver of unexpected type: $receiver")
        }
        val y: Expr[Post]  = dispatch(newVal)
        val x: Expr[Post] = dispatch(receiver)
        // here the static type is desirable
        val cls: ByReferenceClass[Pre] = getClsFromType(receiver.t)
        val isPrivate = fieldRef.decl.flags.exists{
          case Private() => true
          case _ => false
        }
        val isModifiable = fieldRef.decl.flags.exists{
          case Modifiable() => true
          case _ => false
        }
        if (isPrivate) {
          val modFields: Seq[InstanceField[Pre]] = getAllModifiableFields(cls)
          val modVarsNew: Seq[Variable[Pre]] = modFields
            .map(declareNewVar(_, "new"))
          val modVarsOld: Seq[Variable[Pre]] = modFields
            .map(declareNewVar(_, "old"))
          val modVarsNewPost = modVarsNew.map(variables.dispatch)
          val modVarsOldPost = modVarsOld.map(variables.dispatch)
          val modFieldSub = Substitute(
            (modFields
              .map(f =>
                Deref(ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]), f.ref.asInstanceOf[Ref[Pre, InstanceField[Pre]]])(PanicBlame("sub node")))
              zip
              modVarsNew.map(v => Local[Pre](v.ref)))
              .toMap[Expr[Pre], Expr[Pre]]
              +
              (ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]) -> receiver)
          )
          val subbedInv: Expr[Post] = dispatch(modFieldSub.dispatch(cls.ucInvariant))

          val splitInv = SplitInvariant(
            dispatch(Substitute(
              Map[Expr[Pre], Expr[Pre]](ThisObject(cls.ref[Class[Pre]]) -> receiver)
            ).dispatch(cls.ucInvariant)),
            x,
            modFields
              .map(m => succ[Declaration[Post]](m))
              .lazyZip(modVarsNewPost.map(v => Local[Post](v.ref)))
              .lazyZip(modVarsOldPost.map(v => Local[Post](v.ref)))
              .toSeq
          )

          val leakableAssign = if (isModifiable)
            Assign(Local[Post](modVarsNewPost(modFields.indexOf(fieldRef.decl)).ref), y)(PanicBlame("assign local <- local should never fail"))
          else
            assign.rewriteDefault()

          Block(Seq(
            Assert(
              Or(Greater(curPermLeakable(x), IntegerValue(0)),
                Greater(curPermHidden(x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(x,
              ifBody = Scope(modVarsNewPost ++ modVarsOldPost, Block(Seq(
                Inhale(Implies(And(LowEvent(), Low(x)), subbedInv)),
                Inhale(Implies(Not(And(LowEvent(), Low(x))), splitInv)),
                leakableAssign,
                Assert(Implies(And(LowEvent(), Low(x)), subbedInv))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"Invariant: $subbedInv might not hold after assignment"))),
                Assert(Implies(Not(And(LowEvent(), Low(x))), splitInv))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"Invariant: $splitInv might not hold after assignment"))),
              ))
              ),
              elseBody = assign.rewriteDefault())
          ))
        } else {
          if (isModifiable) {
            logger.warn(s"Field $fieldRef is public, no need to annotate it with 'modifiable'.")
          }
          // public / protected / package-private
          Block(Seq(
            Assert(
              Or(Greater(curPermLeakable(x), IntegerValue(0)),
                Greater(curPermHidden(x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(x,
              ifBody =Block(
                (if(noPrimitiveType(newVal.t)) Seq(Assert(leakable(y))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$y must be leakable."))))
                else Seq())
                  ++
                Seq[Statement[Post]](
                  Assert(LowEvent())(_ => assign.blame.blame(AssignFailedSIFUC(assign, "This assignment must be lowEvent."))),
                  Assert(Low(x))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"The receiver $x should be low."))),
                  Assert(Low(y))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$y should be low."))),
                )
              ),
              elseBody = assign.rewriteDefault())
          ))

        }

      case b@Branch(branches: Seq[(Expr[Pre], Statement[Pre])]) =>
        Block[Post](
          branches.map { case (cond: Expr[Pre], _) => Assert(Low(dispatch(cond)))(PanicBlame("If condition might not be low")) }
            :+ b.rewriteDefault()
        )
      case l: Loop[_] =>
        val cond = dispatch(l.cond)
        val assertLowCond: Assert[Post] = Assert(Low(cond))(PanicBlame("Loop condition might not be low"))
        Block[Post](Seq(
          l.rewrite(
            init = Block[Post](Seq(
              l.init.rewriteDefault(),
              assertLowCond
            )),
            update = Block[Post](Seq(
              l.update.rewriteDefault(),
              assertLowCond
            ))
          )
        ))

      case other => other.rewriteDefault()
    }
  }

  private def splitExprUnaryRel(exp: Expr[Pre]): (Expr[Pre], Expr[Pre]) = {
    val unaryInv = PredicateExpSubstitute((e: Expr[Pre]) => e match {
      case LowEvent() | Low(_) => true
      case _ => false
    }, (_:Expr[Pre]) => tt[Pre]).dispatch(exp)
    // this works even though it is redundant -> in the encoding first unaryInv is always inhaled
    // and then low(receiver) ==> relInv
    // in the case of low(receiver) the unary parts of the invariant are inhaled twice (not a problem since all permission amounts can only be wildcard)
    val relInv = exp
    (unaryInv, relInv)
  }

  private def isUnary(e: Expr[Pre]) : Boolean = e.collect {
    case LowEvent() => true
    case Low(_) => true
  }.isEmpty

  private def getClsFromType[G](t: Type[G]): ByReferenceClass[G] = t match {
      case tClass: TByReferenceClass[_] => tClass.cls.decl match {
        case clazz: ByReferenceClass[_] => clazz
        case _ => throw SIFUCUnsupported(t, "Only supports ByReferenceClasses.")
      }
      case _ => throw SIFUCUnsupported(t, "Only supports ByReferenceClasses.")
    }

  override def dispatch(decl: Declaration[Pre]): Unit = {
    implicit val o: Origin = decl.o
    decl match {
      case pred: Predicate[_] =>
        val predRewritten: Predicate[Post] = pred.rewriteDefault()
        if (o.find[HiddenLeakableToPredicates.HiddenLeakableImpl].nonEmpty) {
          if (o.getPreferredName == hiddenPredName.name(o)) {
            hiddenPredRef = predRewritten.ref
          } else if (o.getPreferredName == leakablePredName.name(o)) {
            leakablePredRef = predRewritten.ref
          }
        }
        allScopes.anySucceed(decl, predRewritten)

      case cons: Constructor[Pre] =>
        val clsPre: ByReferenceClass[Pre] = cons.cls.decl.asInstanceOf[ByReferenceClass[Pre]]
        if(isClsFromLib(clsPre)){
          allScopes.anySucceed(decl, decl.rewriteDefault())
          return
        }
        val argsWithGhostParam: Seq[Variable[Pre]] = cons.args ++
          (if (cons.args.exists(isIndirectlyFromUcGhostParam)) Seq()
          else Seq(new Variable(TBool())(origin(indirectlyFromUcSeqName))))
        val cls: Ref[Post, Class[Post]] = succ(clsPre)
        val contractH = dispatch(cons.contract)
        val derefField: InstanceField[Pre] => Expr[Post] =
          f => Deref[Post](ThisObject(cls), succ(f))(_ => cons.blame.blame(SecondVerificationConstructorLeakFail(cons, s"missing perm for field $f")))

        val newArgsH : Seq[Variable[Post]] = argsWithGhostParam.map(variables.dispatch)
        cons.rewrite(
          args = newArgsH,
            body = cons.body.map(stat => Block[Post](
              Seq(
                Inhale(hiddenWrite(ThisObject(cls))),
                Assume(Low(ThisObject(cls))),
                isCurrentMethod2ndVerification.having(false){
                  currentIndirectlyFromUcParam.having(newArgsH.filter(isIndirectlyFromUcGhostParam).head) {
                    dispatch(stat)
                  }
                },
              )
                ++
                inhaleNullFieldsLeakableHidden(clsPre, derefField)
            )),
            contract = contractH.copy(ensures =
              SplitAccountedPredicate(
                contractH.ensures,
                UnitAccountedPredicate(Low(ThisObject(cls))),
              )
            )(PanicBlame("Every constructor always ensures low('this')")),
          ).succeed(cons)

        if(!cons.isPrivate){
          val argSub = new ArgSubstitute(cons.args, cons.outArgs, cons.typeArgs)
          val newArgs = variables.dispatch(argSub.newArgs)
          val leakThis = encodeLeak(ThisObject(clsPre.ref),
              msg => err => cons.blame.blame(SecondVerificationConstructorLeakFail(cons, msg)))

          classDeclarations.declare(
            new Constructor(
              cls,
              newArgs,
              variables.dispatch(argSub.newOutArgs),
              variables.dispatch(argSub.newTypeArgs),
              cons.body.map(stat => {
                Block(inhaleAllLowAndLeakable(argSub.newArgs, newArgs)
                    ++
                    Seq[Statement[Post]](
                      Inhale(hiddenWrite(ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      Assume(LowEvent()),
                      isCurrentMethod2ndVerification.having(true){
                        dispatch(argSub.dispatch(stat))
                      },
                    )
                  ++
                  inhaleNullFieldsLeakableHidden(clsPre, derefField)
                  :+ leakThis
                )
              }
              ),
              ApplicableContract(emptyAccountedPredicate,
                getAccountedPredicate(Seq(
                  leakable(ThisObject(cls)),
                  Low(ThisObject(cls))
                )),
                //TODO check other contract parameters
                tt,
                cons.contract.signals.map(sig => dispatch(argSub.dispatch(sig))),
                Seq(),
                Seq(),
                None
              )(PanicBlame("SIF Encoding postcondition should never be unsatisfiable")),
              false,
              false,
            )(SecondConstructorVerificationFailed(cons))(origin("constructor_l"))
          )
        }
      case m: InstanceMethod[_] =>
        val cls: Ref[Post, Class[Post]] = succ(currentClass.top)
        val argsWithGhostParam: Seq[Variable[Pre]] = m.args ++
          (if (m.args.exists(isIndirectlyFromUcGhostParam)) Seq()
          else Seq(new Variable(TBool())(origin(indirectlyFromUcSeqName))))
        val newArgsH : Seq[Variable[Post]] = argsWithGhostParam.map(variables.dispatch)
        classDeclarations.succeed(m,
          isCurrentMethod2ndVerification.having(false) {
            currentIndirectlyFromUcParam.having(newArgsH.filter(isIndirectlyFromUcGhostParam).head) {
              m.rewrite(args = newArgsH)
            }
          }
        )
        if(isClsFromLib(currentClass.top)){
          return
        }
        if(!m.isPrivate){
          if(m.outArgs.size > 1){
            throw SIFUCUnsupported(m, "Method has too many outArgs")
          }

          if(!m.returnType.isInstanceOf[TVoid[Pre]]){
            throw SIFUCUnsupported(m, "At this point the return type should always be void")
          }
          val argSub = new ArgSubstitute(m.args, m.outArgs, m.typeArgs)
          val newArgs = variables.dispatch(argSub.newArgs)
          val retVar: Seq[Variable[Post]] = argSub.newOutArgs
            .map(variables.dispatch)
          classDeclarations.declare(
            new InstanceMethod(dispatch(argSub.dispatch(m.returnType)),
              newArgs,
              retVar,
              variables.dispatch(argSub.newTypeArgs),
              m.body.map(stat => Block(
                  inhaleAllLowAndLeakable(argSub.newArgs, newArgs)
                    ++
                    Seq[Statement[Post]](
                      Assume(LowEvent()),
                      Inhale(leakable(ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      isCurrentMethod2ndVerification.having(true) {
                        dispatch(argSub.dispatch(stat))
                      },
                    )
              )),
              ApplicableContract(emptyAccountedPredicate,
                retVar.headOption.map(ret => getAccountedPredicate(
                  Option.when(noPrimitiveType(argSub.newOutArgs.head.t))(leakable(Local(ret.ref))).toSeq
                    ++ Option.when(!ret.t.isInstanceOf[TVoid[Post]])(Low(Local(ret.ref[Variable[Post]]))).toSeq)
                  )
                  .getOrElse(emptyAccountedPredicate),
                //TODO check other contract parameters
                tt,
                m.contract.signals.map(sig => dispatch(argSub.dispatch(sig))),
                Seq(),
                Seq(),
                None
              )(PanicBlame("SIF Encoding postcondition should never be unsatisfiable")),
              false,
              false,
              false
          )(SecondMethodVerificationFailed(m))(origin(m.o.getPreferredNameOrElse(Seq("unknown_method"))))
          )
        }

      case cls: ByReferenceClass[_] =>
        currentClass.having(cls) {
          val value = cls.rewriteDefault()
          allScopes.anySucceed(cls, value)
        }
      case declaration: ClassDeclaration[_] =>
        allScopes.anySucceed(decl, decl.rewriteDefault())
      case other => allScopes.anySucceed(decl, decl.rewriteDefault())
    }
  }

  private def isClsFromLib(clsPre: ByReferenceClass[Pre]): Boolean =
    clsPre.o.get[ReadableOrigin].readable.underlyingPath.exists(path => path.startsWith("/home/nicolas/dev/MasterThesis/code/vercors/res"))
}

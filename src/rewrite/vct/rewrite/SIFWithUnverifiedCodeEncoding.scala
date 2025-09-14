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
import vct.rewrite.HiddenLeakableToPredicates.{arrHiddenPredName, arrLeakablePredName, hiddenPredName, leakablePredName}
import vct.rewrite.SIFWithUnverifiedCodeEncoding.{indirectlyFromUcGhostParamName, indirectlyFromUcSeqName}

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

case class HighBranchBlame(app: ContractApplicable[_], reason: String)
  extends Blame[VerificationFailure] {

  override def blame(error: VerificationFailure): Unit = {
    app.blame.blame(SIFUCHighBranchingFailure(app, reason))
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
    val ghostParamValue: Expr[Post] = Local(currentIndirectlyFromUcParam.top.ref[Variable[Post]])(origin(indirectlyFromUcSeqName))
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
        Inhale(leakable(f.t, fieldAccess(f))),
          Inhale(hiddenWrite(f.t, fieldAccess(f)))
        )))))
  }

  private def encodeLeak(objPre: Expr[Pre], blameWithMsg: String => Blame[VerificationFailure])(implicit o: Origin): Statement[Post] = {
    if(objPre.t.asArray.flatMap(tArr => tArr.element.asByReferenceClass).nonEmpty){
      return encodeLeakArray(objPre, blameWithMsg);
    }
    val obj = dispatch(objPre)
    val cls: ByReferenceClass[Pre] = getClsFromType(objPre.t)
    val inv: Expr[Post] = dispatch(
      Substitute(Map[Expr[Pre], Expr[Pre]](ThisObject(cls.ref.asInstanceOf[Ref[Pre, Class[Pre]]]) -> objPre))
        .dispatch(cls.ucInvariant)
    )
    Block(Seq[Statement[Post]](
      Assert(
        Or(Greater(curPermLeakable(objPre.t, obj), IntegerValue(0)),
          Greater(curPermHidden(objPre.t, obj), IntegerValue(0)))
      )(blameWithMsg(s"$obj should either be leakable or hidden")),
      Branch(Seq((Eq(curPermLeakable(objPre.t, obj), IntegerValue(0)),
        Block(Seq[Statement[Post]](
          Exhale(hiddenWrite(objPre.t, obj))(blameWithMsg(s"Might not have write perm to hidden($obj) during leak")),
          Inhale(leakable(objPre.t, obj)),
          Assert(LowEvent())(blameWithMsg("leak might not be lowEvent")),
          Assert(Low(obj))(blameWithMsg(s"$obj might not be low")),
          Exhale(inv)(blameWithMsg(s"failed during exhaling inv: inv")),
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
                  (if(noPrimitiveType(f.t)) Seq(Assert(leakable(f.t, fDeref))(blameWithMsg(s"field might not be leakable: $f")))
                  else Seq())
                  :+
                  Exhale(Perm(FieldLocation[Post](obj, succ(f)), WritePerm()))(blameWithMsg(s"missing write perm for field: $f"))
              )
            })
        ))
      )
      )))
  }

  private def encodeLeakArray(objPre: Expr[Pre], blameWithMsg: String => Blame[VerificationFailure])(implicit o: Origin): Statement[Post] = {
    val elemTypeOpt: Option[TByReferenceClass[Pre]] = objPre.t.asArray.flatMap(_.element.asByReferenceClass)
    if(elemTypeOpt.isEmpty){
      throw SIFUCUnsupported(objPre, s"Unsupported array type: ${objPre.t}")
    }
    val elemType = elemTypeOpt.get

    val obj = dispatch(objPre)
    val len = Length(obj)(blameWithMsg(s"Array $obj might be null."))

    val starAllElem: (Local[Post] => Expr[Post]) => Expr[Post]  = body => starAllArrElem(obj, body, blameWithMsg)

    Block(Seq[Statement[Post]](
      Assert(
        Or(Greater(curPermLeakable(objPre.t, obj), IntegerValue(0)),
          Greater(curPermHidden(objPre.t, obj), IntegerValue(0)))
      )(blameWithMsg(s"$obj should either be leakable or hidden")),
      Branch(Seq((Eq(curPermLeakable(objPre.t, obj), IntegerValue(0)),
        Block(Seq[Statement[Post]](
          Exhale(hiddenWrite(objPre.t, obj))(blameWithMsg(s"Might not have write perm to hidden($obj) during leak")),
          Inhale(leakable(objPre.t, obj)),
          Assert(Low(obj))(blameWithMsg(s"$obj might not be low")),
          Assert(LowEvent())(blameWithMsg("leak might not be lowEvent")),
          Assert(Low(len))(blameWithMsg(s"Length of array $obj might not be low")),
          // only support arrays of Class types -> always assert leakable(elem)
          Assert(starAllElem(i => Star(
            leakable(elemType, ArraySubscript(obj, i)(blameWithMsg(s"ArraySubscript error: $obj"))),
            Low(ArraySubscript(obj, i)(blameWithMsg(s"ArraySubscript error: $obj")))))
          )(blameWithMsg(s"Elements of array $obj might not be low")),
          Exhale(starAllElem(i => Perm(ArrayLocation(obj, i)(blameWithMsg(s"ArrayLocation error: $obj")), WritePerm()))
          )(blameWithMsg(s"Permissions missing for elements of array $obj"))
        ))
      )))
    ))
  }

  private def starAllArrElem(arr: Expr[Post], body: Local[Post] => Expr[Post], blameWithMsg: String => Blame[VerificationFailure])(implicit o : Origin): Starall[Post] = {
      val len = Length(arr)(blameWithMsg(s"Array $arr might be null."))
      val index: Variable[Post] = new Variable(TInt())
      val indexLocal: Local[Post] = Local(index.ref)
      Starall(Seq(index),
        Seq(Seq(ArraySubscript(arr, indexLocal)(blameWithMsg(s"ArraySubscript error: $arr")))),
        Implies(SetMember(indexLocal, RangeSet(IntegerValue(0), len)),
          body(indexLocal)))(blameWithMsg(s"Receiver not injective $arr"))
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

  private def getHiddenPredRef(t : Type[_]) : Ref[Post, Predicate[Post]] =
    if(t.isInstanceOf[TArray[_]])
      arrHiddenPredRef
    else
      hiddenPredRef

  private def getLeakablePredRef(t : Type[_]) : Ref[Post, Predicate[Post]] =
    if(t.isInstanceOf[TArray[_]])
      arrLeakablePredRef
    else
      leakablePredRef

  private def hiddenWrite(t: Type[Pre], obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    Perm(
      PredicateLocation(PredicateApply(getHiddenPredRef(t), Seq(obj))),
      WritePerm(),
    )

  private def leakable(t: Type[Pre], obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    // leakable read and write permissions can be used interchangeably
    Value(PredicateLocation(PredicateApply(getLeakablePredRef(t), Seq(obj))))

  private def curPermHidden(t: Type[Pre], obj: Expr[Post])(implicit o:Origin): Expr[Post] =
    CurPerm(PredicateLocation(PredicateApply(getHiddenPredRef(t), Seq(obj))))

  private def curPermLeakable(t: Type[Pre], obj: Expr[Post])(implicit o:Origin): Expr[Post] =
    CurPerm(PredicateLocation(PredicateApply(getLeakablePredRef(t), Seq(obj))))

  private def inhaleAllLowAndLeakable(variablesPre: Seq[Variable[Pre]], variablesPost: Seq[Variable[Post]])(implicit o : Origin) : Seq[Statement[Post]] = {
    val variables: Seq[(Variable[Pre], Variable[Post])] = variablesPre zip variablesPost
    variables.filter(arg => noPrimitiveType(arg._1.t))
      .map {
        case (vPre, vPost) => Inhale(leakable(vPre.t, Local(vPost.ref[Variable[Post]])))
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

  private def ifLeakableElse(t: Type[Pre], conditionVariable: Expr[Post], ifBody: Statement[Post], elseBody: Statement[Post])(implicit o:Origin) : Statement[Post] =
    Branch(Seq(
      (Greater(curPermLeakable(t, conditionVariable), IntegerValue(0)), ifBody),
      (tt, elseBody)
    ))

  private def ifLeakable(conditionVariable: Expr[Post], ifBody: Statement[Post])(implicit o:Origin) : Statement[Post] =
    Branch(Seq((Greater(curPermLeakable(TAny(), conditionVariable), IntegerValue(0)), ifBody)))

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
  var arrHiddenPredRef: Ref[Post, Predicate[Post]] = null
  var arrLeakablePredRef: Ref[Post, Predicate[Post]] = null

  val currentClass: ScopedStack[ByReferenceClass[Pre]] = ScopedStack()
  val currentMethodOrConstructor: ScopedStack[ContractApplicable[Pre]] = ScopedStack()
  val currentIndirectlyFromUcParam: ScopedStack[Variable[Post]] = ScopedStack()

  override def dispatch(expr: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = expr.o
    expr match {
      // TODO: ternary operator low cond
      //case s@Select(cond, _, _) => Asserting(Low(dispatch(cond)), s.rewriteDefault())(PanicBlame(s"ternary op $s with high condition $cond"))
      case other => other.rewriteDefault() }
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
          args = if (isClsFromLib(cls) || cls.isUnverified) invCons.args.map(dispatch)
                  else setIndirectlyFromUC(invCons.ref.decl.args, invCons.args)
        )
        if(cls.isUnverified){
          Block(
            args.map { arg =>
              Assert(Low(arg))(err => invCons.blame.blame(InvocationSIFUCFailure(invCons, err.failure)))(arg.o)
            }
              ++
              (invCons.args zip args).filter(arg => noPrimitiveType(arg._1.t))
              .map{arg => Assert(leakable(arg._1.t, arg._2))(err => invCons.blame.blame(InvocationSIFUCFailure(invCons, err.failure)))(arg._2.o)}
              ++
            Seq[Statement[Post]](
              Assert(LowEvent())(_ => invCons.blame.blame(InvocationMustBeLowEvent(invCons))),
              newInv,
              Assume(Not(Eq(res, ThisObject[Post](succ(insideClass)))))(invCons.o), // see unverifiedcode/NewObjNotEqToThis.java
              Assume(Low(res))(invCons.o),
              Inhale(leakable(invCons.out.t, res)),
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
          args = if (isClsFromLib(cls) || cls.isUnverified) mInv.args.map(dispatch)
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
                .map { arg => Assert(leakable(arg._1.t, arg._2))(err => mInv.blame.blame(InvocationSIFUCFailure(mInv, err.failure)))(arg._2.o) }
              ++
              Seq[Statement[Post]](
                Assert(LowEvent())(_ => mInv.blame.blame(InvocationMustBeLowEvent(mInv))),
                Assert(Low(dispatch(mInv.obj)))(err => mInv.blame.blame(InvocationSIFUCFailure(mInv, err.failure)))(mInv.obj.o),
                newInv,
                Assume(Low(res))
              )
              ++ (if (noPrimitiveType(mInv.outArgs.head.t)) Seq(Inhale(leakable(mInv.outArgs.head.t, res))) else Seq())
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
                Or(Greater(curPermLeakable(receiver.t, x), IntegerValue(0)),
                  Greater(curPermHidden(receiver.t, x), IntegerValue(0)))
              )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
              ifLeakableElse(receiver.t, x,
                ifBody = Scope(modVarsPost, Block(
                  Seq[Statement[Post]](
                  Inhale(dispatch(unaryInv)),
                  Inhale(Implies(Low(x), dispatch(relInv))),
                  Assign(y, Local[Post](modVarsPost(modFields.indexOf(fieldRef.decl)).ref))(PanicBlame("assign local <- local should never fail")),
                ))),
                elseBody = assign.rewriteDefault())
            ))
          } else {
            Block(Seq(
              Assert(
                Or(Greater(curPermLeakable(receiver.t, x), IntegerValue(0)),
                  Greater(curPermHidden(receiver.t, x), IntegerValue(0)))
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
              Or(Greater(curPermLeakable(receiver.t, x), IntegerValue(0)),
                Greater(curPermHidden(receiver.t, x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(receiver.t, x,
              ifBody = Scope(Seq(tempVar), Block(
                (if(noPrimitiveType(fieldRef.decl.t)) Seq(Inhale(leakable(fieldRef.decl.t, temp))) else Seq())
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

          val leakableAssign = if (isModifiable)
            Assign(Local[Post](modVarsNewPost(modFields.indexOf(fieldRef.decl)).ref), y)(PanicBlame("assign local <- local should never fail"))
          else
            assign.rewriteDefault()

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

          Block(Seq(
            Assert(
              Or(Greater(curPermLeakable(receiver.t, x), IntegerValue(0)),
                Greater(curPermHidden(receiver.t, x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(receiver.t, x,
              ifBody = Scope(modVarsNewPost ++ modVarsOldPost, Block(
                Seq(
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
              Or(Greater(curPermLeakable(receiver.t, x), IntegerValue(0)),
                Greater(curPermHidden(receiver.t, x), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$x must be either hidden or leakable."))),
            ifLeakableElse(receiver.t, x,
              ifBody =Block(
                (if(noPrimitiveType(newVal.t)) Seq(Assert(leakable(newVal.t, y))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$y must be leakable."))))
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

      // Array reads
      case assign @ Assign(resVar @ Local(_), ArraySubscript(a, i)) =>
        if(!a.isInstanceOf[Local[Pre]]){
          logger.warn(s"array of unexpected type: $a")
        }
        val elemTypeOpt: Option[TByReferenceClass[Pre]] = a.t.asArray.flatMap(_.element.asByReferenceClass)
        if(elemTypeOpt.isEmpty){
          throw SIFUCUnsupported(a, s"Unsupported array type: ${a.t}")
        }
        val elemType = elemTypeOpt.get
        val y: Local[Post]  = dispatch(resVar).asInstanceOf[Local[Post]]
        val arr: Expr[Post] = dispatch(a)
        val index: Expr[Post] = dispatch(i)
        // here the static type is desirable
        val tempVar: Variable[Post] = variables.dispatch(new Variable(elemType))
        val temp: Local[Post] = Local(tempVar.ref)
        Block(Seq(
          Assert(
            Or(Greater(curPermLeakable(a.t, arr), IntegerValue(0)),
              Greater(curPermHidden(a.t, arr), IntegerValue(0)))
          )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$arr must be either hidden or leakable."))),
          ifLeakableElse(a.t, arr,
            ifBody = Scope(Seq(tempVar), Block(
              arrayAccessPreconds(assign, arr, index) ++
                Seq[Statement[Post]](
                  // we only support arrays of class type -> always inhale leakable
                  Inhale(leakable(elemType, temp)),
                  Assume(Implies(And(Low(arr), Low(index)), Low(temp))),
                  Assign(y, temp)(PanicBlame("assign local <- local should never fail")),
                ))),
            elseBody = assign.rewriteDefault())
        ))
      // Array writes
      case assign @ Assign(ArraySubscript(a, i), newVal) =>
        if(!a.isInstanceOf[Local[Pre]]){
          logger.warn(s"array of unexpected type: $a")
        }
        val y: Expr[Post]  = dispatch(newVal)
        val arr: Expr[Post] = dispatch(a)
        val index: Expr[Post] = dispatch(i)

          Block(Seq(
            Assert(
              Or(Greater(curPermLeakable(a.t, arr), IntegerValue(0)),
                Greater(curPermHidden(a.t, arr), IntegerValue(0)))
            )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$arr must be either hidden or leakable."))),
            ifLeakableElse(a.t, arr,
              ifBody = Block(arrayAccessPreconds(assign, arr, index) ++
                Seq[Statement[Post]](
                    Assert(leakable(newVal.t, y))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$y must be leakable."))),
                    Assert(LowEvent())(_ => assign.blame.blame(AssignFailedSIFUC(assign, "This assignment must be lowEvent."))),
                    Assert(Low(arr))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"The array $arr should be low."))),
                    Assert(Low(index))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"The index $index should be low."))),
                    Assert(Low(y))(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"$y should be low."))),
                  )
              ),
              elseBody = assign.rewriteDefault()
            )
          ))
      case iProc : InvokeProcedure[_] =>
        if (iProc.ref.decl.o.getPreferredName.get.snake.startsWith("make_array_initialized")) {
          val res = dispatch(iProc.outArgs.head)
          Block(Seq[Statement[Post]](
            Assert(LowEvent())(_ => iProc.blame.blame(InvocationMustBeLowEvent(iProc))),
            iProc.rewriteDefault(),
            Assume(Low(res)),
            Inhale(hiddenWrite(iProc.outArgs.head.t, res)),
          ))
        } else {
          iProc.rewriteDefault()
        }
      case assign@Assign(l: Local[Pre], newArr: NewArray[_]) =>
        val y = dispatch(l)
        Block(Seq[Statement[Post]](
          Assert(LowEvent())(_ => assign.blame.blame(AssignFailedSIFUC(assign, "This assignment of new Array must be lowEvent."))),
          assign.rewriteDefault(),
          Assume(Low(y)),
          Inhale(hiddenWrite(l.t, y)),
        ))

      case b@Branch(branches: Seq[(Expr[Pre], Statement[Pre])]) =>
        Block[Post](
          branches.map { case (cond: Expr[Pre], _) =>
            Assert(Low(dispatch(cond))
              )(HighBranchBlame(currentMethodOrConstructor.top, "If condition might not be low"))
          }
            :+ b.rewriteDefault()
        )
      case l: Loop[_] =>
        val cond = dispatch(l.cond)
        val assertLowCond: Assert[Post] = Assert(Low(cond))(HighBranchBlame(currentMethodOrConstructor.top, "Loop condition might not be low"))
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

  private def assertingArrayAccPreconds(assign: Assign[Pre], arr: Expr[Post], index: Expr[Post], body : Expr[Post])(implicit o : Origin) : Asserting[Post] = {
    val preConds = arrayAccessPreconds(assign, arr, index)
    Asserting(And(preConds.head.res,
      preConds(1).res),
      body)(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"array access preconds failed: $arr, index: $index")))
  }

  private def arrayAccessPreconds(assign: Assign[Pre], arr: Expr[Post], index: Expr[Post])(implicit o: Origin): Seq[Assert[Post]] = {
    Seq[Assert[Post]](
      Assert(Implies(Not(Local(currentIndirectlyFromUcParam.top.ref[Variable[Post]])),
        indexInBounds(assign, arr, index))
      )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"not coming from UC and index $index out of bounds for $arr"))),
      Assert(Implies(Not(indexInBounds(assign, arr, index)),
        And(
          Low(Length(arr)(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"array might be null: $arr")))),
          Low(index)
        )
      )
      )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"coming from UC. either: index $index out of bounds for $arr or index/length not low"))),
    )
  }

  private def fieldAccessPreconds(assign: Assign[Pre], receiver: Expr[Post])(implicit o: Origin): Seq[Assert[Post]] = {
    Seq[Assert[Post]](
      Assert(Implies(Not(Local(currentIndirectlyFromUcParam.top.ref[Variable[Post]])),
        Neq(receiver, Null()))
      )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"not coming from UC and index receiver $receiver might be null"))),
      Assert(Low(Neq(receiver, Null()))
      )(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"whether receiver $receiver is nonnull might be high"))),
      )
  }

  private def indexInBounds(assign: Assign[Pre], arr: Expr[Post], index: Expr[Post])(implicit o : Origin) = {
    And(
      LessEq(IntegerValue(0), index),
      Less(index, Length(arr)(_ => assign.blame.blame(AssignFailedSIFUC(assign, s"array $arr might be null."))))
    )
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
      case TArray(_ : TByReferenceClass[_]) => throw SIFUCUnsupported(t, "should not happen")
      case _ : TArray[_] => throw SIFUCUnsupported(t, "Primitive type arrays are not supported")
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
          } else if (o.getPreferredName == arrHiddenPredName.name(o)) {
              arrHiddenPredRef = predRewritten.ref
          } else if (o.getPreferredName == leakablePredName.name(o)) {
            leakablePredRef = predRewritten.ref
          } else if (o.getPreferredName == arrLeakablePredName.name(o)) {
              arrLeakablePredRef = predRewritten.ref
          }
        }
        allScopes.anySucceed(decl, predRewritten)

      case cons: Constructor[Pre] =>
        val clsPre: ByReferenceClass[Pre] = cons.cls.decl.asInstanceOf[ByReferenceClass[Pre]]
        if(isClsFromLib(clsPre) || currentClass.top.isUnverified){
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
                Inhale(hiddenWrite(TAny(), ThisObject(cls))),
                Assume(Low(ThisObject(cls))),
                  currentIndirectlyFromUcParam.having(newArgsH.filter(isIndirectlyFromUcGhostParam).head) {
                    currentMethodOrConstructor.having(cons) {
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
          val argSub = new ArgSubstitute(argsWithGhostParam, cons.outArgs, cons.typeArgs)
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
                val fromUcParam = newArgs.filter(isIndirectlyFromUcGhostParam).head
                Block(inhaleAllLowAndLeakable(argSub.newArgs, newArgs)
                    ++
                    Seq[Statement[Post]](
                      Assign(Local(fromUcParam.ref[Variable[Post]]), tt)(PanicBlame("reassigning fromUC=true should never fail!")),
                      Inhale(hiddenWrite(TAny(), ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      Assume(LowEvent()),
                      currentIndirectlyFromUcParam.having(fromUcParam) {
                        currentMethodOrConstructor.having(cons) {
                          dispatch(argSub.dispatch(stat))
                        }
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
                  leakable(TAny(), ThisObject(cls)),
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
        if(isClsFromLib(currentClass.top) || currentClass.top.isUnverified){
          classDeclarations.succeed(m, m.rewriteDefault())
          return
        }
        val argsWithGhostParam: Seq[Variable[Pre]] = m.args ++
          (if (m.args.exists(isIndirectlyFromUcGhostParam)) Seq()
          else Seq(new Variable(TBool())(origin(indirectlyFromUcSeqName))))
        val newArgsH : Seq[Variable[Post]] = argsWithGhostParam.map(variables.dispatch)
        classDeclarations.succeed(m,
          currentMethodOrConstructor.having(m) {
            currentIndirectlyFromUcParam.having(newArgsH.filter(isIndirectlyFromUcGhostParam).head) {
              m.rewrite(args = newArgsH)
            }
          }
        )
        if(!m.isPrivate){
          if(m.outArgs.size > 1){
            throw SIFUCUnsupported(m, "Method has too many outArgs")
          }

          if(!m.returnType.isInstanceOf[TVoid[Pre]]){
            throw SIFUCUnsupported(m, "At this point the return type should always be void")
          }
          val argSub = new ArgSubstitute(argsWithGhostParam, m.outArgs, m.typeArgs)
          val newArgs = variables.dispatch(argSub.newArgs)
          val retVar: Seq[Variable[Post]] = argSub.newOutArgs
            .map(variables.dispatch)
          classDeclarations.declare(
            new InstanceMethod(dispatch(argSub.dispatch(m.returnType)),
              newArgs,
              retVar,
              variables.dispatch(argSub.newTypeArgs),
              m.body.map(stat => {
                val fromUcParam = newArgs.filter(isIndirectlyFromUcGhostParam).head
                Block(
                  inhaleAllLowAndLeakable(argSub.newArgs, newArgs)
                    ++
                    Seq[Statement[Post]](
                      Assign(Local(fromUcParam.ref[Variable[Post]]), tt)(PanicBlame("reassigning fromUC=true should never fail!")),
                      Assume(LowEvent()),
                      Inhale(leakable(TAny(), ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      currentIndirectlyFromUcParam.having(fromUcParam) {
                        currentMethodOrConstructor.having(m) {
                          dispatch(argSub.dispatch(stat))
                        }
                      },
                    )
                )
              }),
              ApplicableContract(emptyAccountedPredicate,
                retVar.headOption.map(ret => getAccountedPredicate(
                  Option.when(noPrimitiveType(argSub.newOutArgs.head.t))(leakable(argSub.newOutArgs.head.t, Local(ret.ref))).toSeq
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

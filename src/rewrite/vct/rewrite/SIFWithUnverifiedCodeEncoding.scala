package vct.rewrite

import com.typesafe.scalalogging.LazyLogging
import hre.util.ScopedStack
import vct.col.ast.{InstanceField, _}
import vct.col.origin._
import vct.col.ref.Ref
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder, Rewritten}
import vct.col.util.AstBuildHelpers.tt
import vct.col.util.Substitute
import vct.result.VerificationError.SystemError
import vct.rewrite.HiddenLeakableToPredicates.{hiddenPredName, leakablePredName}

case object SIFWithUnverifiedCodeEncoding extends RewriterBuilder {
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

case class InsufficientPermissionDuringLeak(leak: Leak[_])
    extends Blame[AssertFailed] {
  override def blame(error: AssertFailed): Unit =
    leak.blame.blame(LeakInsufficientPermission(leak, error.failure))
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
    val newArgs : Seq[Variable[Pre]] = oldArgs.map(declareNewVar)
    val newOutArgs: Seq[Variable[Pre]] = oldOutArgs.map(declareNewVar)
    // TypeArgs do not seem to be supported by VerCors currently
    val newTypeArgs: Seq[Variable[Pre]] = oldTypeArgs.map(declareNewVar)

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

  private def noPrimitiveType(t: Type[Post]): Boolean =
    !t.isInstanceOf[PrimitiveType[Post]]

  private def encodeLeak(
                          obj: Expr[Post]
                        )(implicit o: Origin): Statement[Post] = {
    // TODO
    Inhale(leakable(obj))
  }

  private def getAllFields: Seq[InstanceField[Pre]] = {
    currentClass.top.decls.collect { case field: InstanceField[_] => field }
  }

  private def noop(implicit o: Origin): Statement[Post] = Block[Post](Seq())

  private def hiddenRead(obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    Value(PredicateLocation(PredicateApply(hiddenPredRef, Seq(obj))))

  private def hiddenWrite(obj: Expr[Post])(implicit o: Origin): Expr[Post] =
    Perm(
      PredicateLocation(PredicateApply(hiddenPredRef, Seq(obj))),
      WritePerm(),
    )

  private def leakable(obj: Expr[Post])(implicit o: Origin): Expr[Post] = {
    // leakable read and write permissions can be used interchangeably
    Value(PredicateLocation(PredicateApply(leakablePredRef, Seq(obj))))
  }

  private def inhaleAllLowAndLeakable(variables: Seq[Variable[Post]])(implicit o : Origin) : Seq[Statement[Post]] =
    variables.filter(arg => noPrimitiveType(arg.t))
      .map(arg => Inhale(leakable(Local(arg.ref[Variable[Post]])))) ++
      variables.map(arg => Assume(Low(Local(arg.ref[Variable[Post]]))))

  private def declareNewVar[G](arg: Variable[G]): Variable[G] = {
    new Variable(arg.t)(origin(
      arg.o.getPreferredNameOrElse(Seq("unknown_var"))
    ))
  }

  private def emptyAccountedPredicate(implicit o:Origin) : AccountedPredicate[Post] = getAccountedPredicate(Seq(tt[Post]))

  private def getAccountedPredicate(exp: Seq[Expr[Post]])(implicit o: Origin): AccountedPredicate[Post] =
    exp match {
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

  private def origin(preferredName: Name): Origin =
    Origin(Seq(IndirectName(preferredName), LabelContext("unverifiedCodeSIF")))

  var hiddenPredRef: Ref[Post, Predicate[Post]] = null
  var leakablePredRef: Ref[Post, Predicate[Post]] = null

  val currentClass: ScopedStack[ByReferenceClass[Pre]] = ScopedStack()

  override def dispatch(expr: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = expr.o
    expr match { case other => other.rewriteDefault() }
  }

  override def dispatch(stat: Statement[Pre]): Statement[Post] = {
    implicit val o: Origin = stat.o
    stat match {
      case l @ Leak(obj) =>
        val newObj = dispatch(obj)
        Assert(Leakable[Post](newObj))(InsufficientPermissionDuringLeak(
          l
        )); // TODO
      case other => other.rewriteDefault()
    }
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
        val cls: Ref[Post, Class[Post]] = succ(cons.cls.decl)
        val contractH = dispatch(cons.contract)

        cons.rewrite(
            body = cons.body.map(stat => Block[Post](
              Seq(
                Inhale(hiddenWrite(ThisObject(cls))),
                Assume(Low(ThisObject(cls))),
                dispatch(stat),
              ))),
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
          classDeclarations.declare(
            new Constructor(
              cls,
              newArgs,
              variables.dispatch(argSub.newOutArgs),
              variables.dispatch(argSub.newTypeArgs),
              cons.body.map(stat => {
                Block(inhaleAllLowAndLeakable(newArgs)
                    ++
                    Seq[Statement[Post]](
                      Inhale(hiddenWrite(ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      Assume(LowEvent()),
                      dispatch(argSub.dispatch(stat)),
                      encodeLeak(ThisObject(cls)),
                    )
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
        classDeclarations.succeed(m, m.rewriteDefault())
        if(!m.isPrivate){
          if(m.outArgs.size > 1){
            throw SIFUCUnsupported(m, "Method has too many outArgs")
          }

          if(!m.returnType.isInstanceOf[TVoid[Pre]]){
            throw SIFUCUnsupported(m, "At this point the return type should always be void")
          }
          val argSub = new ArgSubstitute(m.args, m.outArgs, m.typeArgs)
          val newArgs = variables.dispatch(argSub.newArgs)
          val retVar: Option[Variable[Post]] = argSub.newOutArgs.find(!_.t.isInstanceOf[TVoid[Pre]])
            .map(variables.dispatch)
          classDeclarations.declare(
            new InstanceMethod(dispatch(argSub.dispatch(m.returnType)),
              newArgs,
              retVar.toSeq,
              variables.dispatch(argSub.newTypeArgs),
              m.body.map(stat => Block(
                  inhaleAllLowAndLeakable(newArgs)
                    ++
                    Seq[Statement[Post]](
                      Assume(LowEvent()),
                      Inhale(leakable(ThisObject(cls))),
                      Assume(Low(ThisObject(cls))),
                      dispatch(argSub.dispatch(stat)),
                    )
              )),
              ApplicableContract(emptyAccountedPredicate,
                retVar.map(ret => getAccountedPredicate(
                  Option.when(noPrimitiveType(ret.t))(leakable(Local(ret.ref))).toSeq
                    :+ Low(Local(ret.ref)))
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



}

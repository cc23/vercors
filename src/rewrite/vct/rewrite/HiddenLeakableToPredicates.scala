package vct.rewrite

import vct.col.ast._
import vct.col.origin._
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.util.SuccessionMap
import vct.rewrite.HiddenLeakableToPredicates.{HiddenLeakableImpl, arrHiddenPredName, arrLeakablePredName, hiddenPredName, leakablePredName}

case object HiddenLeakableToPredicates extends RewriterBuilder {
  val hiddenPredName: PreferredName = PreferredName(Seq("hiddenPred"))
  val arrHiddenPredName: PreferredName = PreferredName(Seq("arrHiddenPred"))
  val leakablePredName: PreferredName = PreferredName(Seq("leakablePred"))
  val arrLeakablePredName: PreferredName = PreferredName(Seq("arrLeakablePred"))

  override def key: String = "hiddenLeakableToPreds"

  override def desc: String =
    "Translate the hidden and leakable expressions into predicates."

  case class HiddenLeakableImpl() extends OriginContent {

  }
}

case class HiddenLeakableToPredicates[Pre <: Generation]() extends Rewriter[Pre] {
  val onceStuff : SuccessionMap[String, Predicate[Post]] = SuccessionMap()
  val hiddenPred : Predicate[Post] = new Predicate[Post](Seq(new Variable(TAny())(Origin(Seq(PreferredName(Seq("obj")))))), None, false, false
  )(Origin(Seq(hiddenPredName, HiddenLeakableImpl())))
  val leakablePred : Predicate[Post]= new Predicate[Post](Seq(new Variable(TAny())(Origin(Seq(PreferredName(Seq("obj")))))),
    None, false, false
  )(Origin(Seq(leakablePredName, HiddenLeakableImpl())))
    val arrHiddenPred : Predicate[Post] = new Predicate[Post](Seq(new Variable(TAny())(Origin(Seq(PreferredName(Seq("arr")))))), None, false, false
  )(Origin(Seq(arrHiddenPredName, HiddenLeakableImpl())))
  val arrLeakablePred : Predicate[Post]= new Predicate[Post](Seq(new Variable(TAny())(Origin(Seq(PreferredName(Seq("arr")))))),
    None, false, false
  )(Origin(Seq(arrLeakablePredName, HiddenLeakableImpl())))

  override def dispatch(loc: Location[Pre]): Location[Post] = {
    implicit val o: Origin = loc.o
    loc match {
      case AmbiguousLocation(Hidden(obj)) if obj.t.asArray.nonEmpty =>
        PredicateLocation(PredicateApply(arrHiddenPred.ref, Seq(dispatch(obj))))
      case AmbiguousLocation(Hidden(obj)) =>
        PredicateLocation(PredicateApply(hiddenPred.ref, Seq(dispatch(obj))))
      case AmbiguousLocation(Leakable(obj)) if obj.t.asArray.nonEmpty =>
        PredicateLocation(PredicateApply(arrLeakablePred.ref, Seq(dispatch(obj))))
      case AmbiguousLocation(Leakable(obj)) =>
        PredicateLocation(PredicateApply(leakablePred.ref, Seq(dispatch(obj))))
      case other => other.rewriteDefault()
    }
  }

  override def dispatch(expr: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = expr.o
    expr match {
      case Hidden(obj) if obj.t.asArray.nonEmpty => PredicateApplyExpr(PredicateApply(arrHiddenPred.ref, Seq(dispatch(obj))))
      case Hidden(obj) => PredicateApplyExpr(PredicateApply(hiddenPred.ref, Seq(dispatch(obj))))
      case Leakable(obj) if obj.t.asArray.nonEmpty => Value(PredicateLocation(PredicateApply(arrLeakablePred.ref, Seq(dispatch(obj)))))
      case Leakable(obj) => Value(PredicateLocation(PredicateApply(leakablePred.ref, Seq(dispatch(obj)))))
      case other => other.rewriteDefault()
    }
  }

  override def dispatch(decl: Declaration[Pre]): Unit = {
    onceStuff.getOrElseUpdate("hiddenPred", {
      globalDeclarations.declare(hiddenPred)
    })
    onceStuff.getOrElseUpdate("leakablePred", {
      globalDeclarations.declare(leakablePred)
    })
    onceStuff.getOrElseUpdate("arrHiddenPred", {
      globalDeclarations.declare(arrHiddenPred)
    })
    onceStuff.getOrElseUpdate("arrLeakablePred", {
      globalDeclarations.declare(arrLeakablePred)
    })
    allScopes.anySucceed(decl, decl.rewriteDefault())
  }
}

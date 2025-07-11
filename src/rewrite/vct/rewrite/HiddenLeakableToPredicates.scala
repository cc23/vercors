package vct.rewrite

import vct.col.ast._
import vct.col.origin._
import vct.col.resolve.lang.Java.JAVA_LANG_OBJECT
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.util.SuccessionMap

case object HiddenLeakableToPredicates extends RewriterBuilder {

  override def key: String = "hiddenLeakableToPreds"

  override def desc: String =
    "Translate the hidden and leakable expressions into predicates."
}

case class HiddenLeakableToPredicates[Pre <: Generation]() extends Rewriter[Pre] {
  val onceStuff : SuccessionMap[String, Predicate[Post]] = SuccessionMap()
  val origin: Origin = new Origin(Seq())
  val hiddenPred : Predicate[Post] = new Predicate[Post](Seq(new Variable(TAny())(origin)), None, false, false)(origin)
  val leakablePred : Predicate[Post]= new Predicate[Post](Seq(new Variable(TAny())(origin)), None, false, false)(origin)

  override def dispatch(loc: Location[Pre]): Location[Post] = {
    implicit val o: Origin = loc.o
    loc match {
      case AmbiguousLocation(Hidden(obj)) =>
        PredicateLocation(PredicateApply(hiddenPred.ref, Seq(dispatch(obj))))
      case AmbiguousLocation(Leakable(obj)) =>
        PredicateLocation(PredicateApply(leakablePred.ref, Seq(dispatch(obj))))
      case other => other.rewriteDefault()
    }
  }

  override def dispatch(expr: Expr[Pre]): Expr[Post] = {
    implicit val o: Origin = expr.o
    expr match {
      case Hidden(obj) => PredicateApplyExpr(PredicateApply(hiddenPred.ref, Seq(dispatch(obj))))
      case Leakable(obj) => Value(PredicateLocation(PredicateApply(leakablePred.ref, Seq(dispatch(obj)))))
      case other => other.rewriteDefault()
    }
  }

  override def dispatch(decl: Declaration[Pre]): Unit = {
    onceStuff.getOrElseUpdate("hiddenPred", {
      globalDeclarations.declare(hiddenPred)
    })
    val obj = JAVA_LANG_OBJECT
    val ttype = TType(JAVA_LANG_OBJECT)
    onceStuff.getOrElseUpdate("leakablePred", {
      globalDeclarations.declare(leakablePred)
    })
    allScopes.anySucceed(decl, decl.rewriteDefault())
  }
}

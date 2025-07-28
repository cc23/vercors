package vct.col.util

import vct.col.ast._
import vct.col.rewrite.NonLatchingRewriter

/** Apply a substitution function to expressions depending on whether they satisfy a predicate
  */
case class PredicateExpSubstitute[G](
    predicate: Expr[G] => Boolean,
    subExp: Expr[G] => Expr[G]
) extends NonLatchingRewriter[G, G] {

  case class SuccOrIdentity() extends SuccessorsProviderTrafo[G, G](allScopes) {
    override def postTransform[T <: Declaration[G]](
        pre: Declaration[G],
        post: Option[T],
    ): Option[T] = Some(post.getOrElse(pre.asInstanceOf[T]))
  }

  override def succProvider: SuccessorsProvider[G, G] = SuccOrIdentity()

  override def dispatch(e: Expr[G]): Expr[G] =
    e match {
      case expr if predicate(expr) => subExp(expr)
      case other => other.rewriteDefault()
    }

}

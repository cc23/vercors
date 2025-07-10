package vct.rewrite

import hre.util.ScopedStack
import vct.col.ast._
import vct.col.origin._
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}

case object ResolveLeak extends RewriterBuilder {
  override def key: String = "leak"
  override def desc: String =
    "Resolve the leak operation for partially verified code."
}

case class InsufficientPermissionDuringLeak(leak: Leak[_])
  extends Blame[AssertFailed] {
  override def blame(error: AssertFailed): Unit =
    leak.blame.blame(LeakInsufficientPermission(leak, error.failure))
}


case class ResolveLeak[Pre <: Generation]()
    extends Rewriter[Pre] {

  val currentResultVar: ScopedStack[Local[Post]] = ScopedStack()


  override def dispatch(stat: Statement[Pre]): Statement[Post] = {
    implicit val o: Origin = stat.o
    stat match {
        case l @ Leak(obj) =>
          val newObj = dispatch(obj)
          Assert(Leakable[Post](newObj))(InsufficientPermissionDuringLeak(l)); //TODO
        case other => other.rewriteDefault()
      }
    }

  override def dispatch(decl: Declaration[Pre]): Unit =
    decl match {
      case cls: ByReferenceClass[_] => allScopes.anySucceed(decl, decl.rewriteDefault()) //TODO get class
      case other => allScopes.anySucceed(decl, decl.rewriteDefault())
    }
}

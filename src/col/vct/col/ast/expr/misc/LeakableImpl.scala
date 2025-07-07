package vct.col.ast.expr.misc

import vct.col.ast.ops.LeakableOps
import vct.col.ast.{Leakable, TBool, Type}
import vct.col.print.{Ctx, Doc, Precedence, Text}

trait LeakableImpl[G] extends LeakableOps[G] {
  this: Leakable[G] =>
  override def t: Type[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc = Text("leakable(") <> expr <> ")"
}

package vct.col.ast.expr.misc

import vct.col.ast.{Low, TBool, Type}
import vct.col.print.{Ctx, Doc, Precedence, Text}
import vct.col.ast.ops.LowOps

trait LowImpl[G] extends LowOps[G] {
  this: Low[G] =>
  override def t: Type[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc = Text("low(") <> expr <> ")"
}

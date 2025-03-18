package vct.col.ast.expr.misc

import vct.col.ast.ops.LowEventOps
import vct.col.ast.{LowEvent, TBool, Type}
import vct.col.print.{Ctx, Doc, Precedence, Text}

trait LowEventImpl[G] extends LowEventOps[G] {
  this: LowEvent[G] =>
  override def t: Type[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc = Text("lowEvent")
}

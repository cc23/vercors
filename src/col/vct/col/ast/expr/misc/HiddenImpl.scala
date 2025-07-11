package vct.col.ast.expr.misc

import vct.col.ast.ops.HiddenOps
import vct.col.ast.{Hidden, TBool, Type}
import vct.col.print.{Ctx, Doc, Precedence, Text}

trait HiddenImpl[G] extends HiddenOps[G] {
  this: Hidden[G] =>
  override def t: Type[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc = Text("hidden(") <> expr <> ")"
}

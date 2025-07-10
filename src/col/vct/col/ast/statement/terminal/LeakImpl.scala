package vct.col.ast.statement.terminal

import vct.col.ast.{Expr, Leak}
import vct.col.ast.ops.LeakOps
import vct.col.print.{Ctx, Doc, Nest, Text}

trait LeakImpl[G] extends LeakOps[G] {
  this: Leak[G] =>
  def layoutSpec(implicit ctx: Ctx): Doc =
    Text("leak") <+> "(" <> Nest(expr.show) <> ")"

  override def layout(implicit ctx: Ctx): Doc =
    Text("leak") <+> "(" <> Nest(expr.show) <> ")"

  override def expr: Expr[G] = obj
}

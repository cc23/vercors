package vct.col.ast.statement.terminal

import vct.col.ast.{Declassify, Expr}
import vct.col.ast.ops.DeclassifyOps
import vct.col.print.{Ctx, Doc, Nest, Text}

trait DeclassifyImpl[G] extends DeclassifyOps[G] {
  this: Declassify[G] =>
//  def layoutSpec(implicit ctx: Ctx): Doc =
//    Text("declassify") <+> "(" <> Nest(expr.show) <> ")"

  override def layout(implicit ctx: Ctx): Doc =
    Text("declassify") <+> "(" <> Nest(expr.show) <> ")"

  override def expr: Expr[G] = this.expr
}

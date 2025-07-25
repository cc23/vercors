package vct.col.ast.expr.misc

import vct.col.ast.ops.SplitInvariantOps
import vct.col.ast.{SplitInvariant, TBool, Type}
import vct.col.print.{Ctx, Doc, Precedence, Text}

trait SplitInvariantImpl[G] extends SplitInvariantOps[G] {
  this: SplitInvariant[G] =>
  override def t: Type[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC
  override def layout(implicit ctx: Ctx): Doc = Text("splitinv(") <> inv <> ")(" <> receiver <> ")(" <>
    Doc.fold(repl.map(r => Text("(") <> ctx.name(r._1) <> ", " <> r._2 <> ", " <> r._3 <> ")"))(_ <+> ", " <+> _) <> ")"}

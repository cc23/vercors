package vct.col.ast.statement.composite

import vct.col.ast.node.NodeFamilyImpl
import vct.col.ast.ops.SIFTryCatchFinallyOps
import vct.col.ast.{Block, SIFTryCatchFinally}
import vct.col.print._

trait SIFTryCatchFinallyImpl[G]
    extends NodeFamilyImpl[G] with SIFTryCatchFinallyOps[G] {
  this: SIFTryCatchFinally[G] =>

  override def layout(implicit ctx: Ctx): Doc =
    Doc.spread(Seq(
      Text("try") <+> body.layoutAsBlock,
      Doc.spread(catches),
      if (after == Block[G](Nil))
        Empty
      else
        Text("finally") <+> after.layoutAsBlock,
    ))
}

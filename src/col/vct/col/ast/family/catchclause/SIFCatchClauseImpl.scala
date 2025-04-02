package vct.col.ast.family.catchclause

import vct.col.ast.ops.{SIFCatchClauseFamilyOps, SIFCatchClauseOps}
import vct.col.ast.util.Declarator
import vct.col.ast.{Declaration, SIFCatchClause}
import vct.col.print._

trait SIFCatchClauseImpl[G] extends Declarator[G] with SIFCatchClauseOps[G] with SIFCatchClauseFamilyOps[G] {
  this: SIFCatchClause[G] =>
  override def declarations: Seq[Declaration[G]] = Seq(decl)

  override def layout(implicit ctx: Ctx): Doc =
    Text("catch") <+> "(" <> decl <> ")" <+> body.layoutAsBlock
}

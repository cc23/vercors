package vct.col.ast.family.fieldflag

import vct.col.ast.Modifiable
import vct.col.ast.ops.ModifiableOps
import vct.col.print.{Ctx, Doc, Text}

trait ModifiableImpl[G] extends ModifiableOps[G] {
  this: Modifiable[G] =>
  override def layout(implicit ctx: Ctx): Doc = Text("modifiable")

}

package vct.col.ast.family.fieldflag

import vct.col.ast.Private
import vct.col.ast.ops.PrivateOps
import vct.col.print.{Ctx, Doc, Text}

trait PrivateImpl[G] extends PrivateOps[G] {
  this: Private[G] =>
  override def layout(implicit ctx: Ctx): Doc = Text("private")

}

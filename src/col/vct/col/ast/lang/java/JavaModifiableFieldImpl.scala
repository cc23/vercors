package vct.col.ast.lang.java

import vct.col.ast.JavaModifiableField
import vct.col.ast.ops.JavaModifiableFieldOps
import vct.col.print.{Ctx, Doc, Text}

trait JavaModifiableFieldImpl[G] extends JavaModifiableFieldOps[G] {
  this: JavaModifiableField[G] =>
  override def layout(implicit ctx: Ctx): Doc = Text("modifiable")
}

package vct.col.ast.lang.java

import vct.col.ast.JavaUnverifiedClass
import vct.col.ast.ops.JavaUnverifiedClassOps
import vct.col.print.{Ctx, Doc, Text}

trait JavaUnverifiedClassImpl[G] extends JavaUnverifiedClassOps[G] {
  this: JavaUnverifiedClass[G] =>
  override def layout(implicit ctx: Ctx): Doc = Text("unverified_class")
}

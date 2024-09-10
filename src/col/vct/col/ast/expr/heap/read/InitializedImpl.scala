package vct.col.ast.expr.heap.read

import vct.col.ast.{Initialized, TBool}
import vct.col.print.{Ctx, Doc, Group, Precedence, Text}

trait InitializedImpl[G] { this: Initialized[G] =>

  override def t: TBool[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc =
    Group(Text("\\initialized(") <> "TODO" <> ")")

}

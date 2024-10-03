package vct.col.ast.expr.heap.read

import vct.col.ast.{OnInit, TBool}
import vct.col.print._

trait OnInitImpl[G] { this: OnInit[G] =>

  override def t: TBool[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc =
    Group(Text("\\onInit(") <> "TODO" <> ")")

}

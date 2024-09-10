package vct.col.ast.expr.heap.read

import vct.col.ast.{TBool, Token}
import vct.col.print.{Ctx, Doc, Group, Precedence, Text}

trait TokenImpl[G] { this: Token[G] =>
  override def t: TBool[G] = TBool()

  override def precedence: Int = Precedence.ATOMIC

  override def layout(implicit ctx: Ctx): Doc =
    Group(Text("\\token(") <> "TODO" <> ")")
}

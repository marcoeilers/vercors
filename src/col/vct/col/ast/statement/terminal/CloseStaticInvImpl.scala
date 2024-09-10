package vct.col.ast.statement.terminal

import vct.col.ast.CloseStaticInv
import vct.col.print.{Ctx, Doc, Show, Text}

trait CloseStaticInvImpl[G] { this: CloseStaticInv[G] =>

  def layoutSpec(implicit ctx: Ctx): Doc =
    Text("close") <+> clz <> ";"

  override def layout(implicit ctx: Ctx): Doc = Doc.inlineSpec(Show.lazily(layoutSpec(_)))


}

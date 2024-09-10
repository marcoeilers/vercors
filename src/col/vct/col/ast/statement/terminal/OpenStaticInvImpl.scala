package vct.col.ast.statement.terminal

import vct.col.ast.OpenStaticInv
import vct.col.print.{Ctx, Doc, Show, Text}

trait OpenStaticInvImpl[G] { this: OpenStaticInv[G] =>

  def layoutSpec(implicit ctx: Ctx): Doc =
    Text("open") <+> clz <> ";"

  override def layout(implicit ctx: Ctx): Doc = Doc.inlineSpec(Show.lazily(layoutSpec(_)))


}

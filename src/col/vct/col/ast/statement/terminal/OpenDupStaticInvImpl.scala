package vct.col.ast.statement.terminal

import vct.col.ast.OpenDupStaticInv
import vct.col.print.{Ctx, Doc, Show, Text}

trait OpenDupStaticInvImpl[G] { this: OpenDupStaticInv[G] =>

  def layoutSpec(implicit ctx: Ctx): Doc =
    Text("open") <+> clz <> ";"

  override def layout(implicit ctx: Ctx): Doc = Doc.inlineSpec(Show.lazily(layoutSpec(_)))


}

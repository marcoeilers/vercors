package vct.col.ast.lang

import vct.col.ast.{JavaNewClass, Type}
import vct.col.print.{Ctx, Doc, DocUtil, Empty, Group, Text}

trait JavaNewClassImpl[G] { this: JavaNewClass[G] =>
  override def t: Type[G] = name

  override def layout(implicit ctx: Ctx): Doc =
    Group(
      Group(Text("new") <+> name <>
        (if(typeArgs.isEmpty) Empty else Text("<") <> Doc.args(typeArgs) <> ">")) <>
        "(" <> Doc.args(args) <> ")" <>
        DocUtil.givenYields(givenArgs, yields)
    )
}
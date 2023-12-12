package vct.col.ast.expr.ambiguous

import vct.col.ast.{AmbiguousOr, TBool, TProcess, Type}
import vct.col.print.{Ctx, Doc, Precedence}
import vct.col.typerules.CoercionUtils

trait AmbiguousOrImpl[G] { this: AmbiguousOr[G] =>
  override lazy val t: Type[G] = if(isProcessOp) TProcess() else TBool()

  override def precedence: Int = Precedence.OR
  override def layout(implicit ctx: Ctx): Doc = lassoc(left, "||", right)
}
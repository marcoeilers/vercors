package vct.col.ast.unsorted

import vct.col.ast.{PVLReceiver, Type}
import vct.col.ast.ops.PVLReceiverOps
import vct.col.print._

trait PVLReceiverImpl[G] extends PVLReceiverOps[G] { this: PVLReceiver[G] =>
  override def layout(implicit ctx: Ctx): Doc = Text("/* PVL */ \\receiver")
  override def t: Type[G] = ref.get.inferredReceiver.get.t
}

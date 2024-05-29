package vct.col.ast.unsorted

import vct.col.ast.ops.ChorStatementOps
import vct.col.ast.{
  Assign,
  Branch,
  ChorStatement,
  Communicate,
  Endpoint,
  EndpointExpr,
  EndpointStatement,
  Expr,
  Loop,
  Statement,
}
import vct.col.print._
import vct.col.ref.Ref
import vct.col.util.AstBuildHelpers

import scala.collection.immutable.ListSet
import scala.util.Try

trait ChorStatementImpl[G] extends ChorStatementOps[G] {
  this: ChorStatement[G] =>
  override def layout(implicit ctx: Ctx): Doc =
    Text("/* choreographic statement */") <+/> inner
  assert(wellformed)
  def wellformed: Boolean =
    inner match {
      // There are only a few statements where we fully define how projection works - for now
      // Probably this fits better in the check pass, but it's fine for now
      case _: Branch[G] | _: Loop[G] => true
      case _ => false
    }

  object branch {
    def apply(): Branch[G] = inner.asInstanceOf[Branch[G]]

    def cond: Expr[G] = branch().branches.head._1
    def guards: Seq[Expr[G]] =
      AstBuildHelpers.unfoldStar(branch().branches.head._1)
    def endpointGuards: Seq[EndpointExpr[G]] =
      guards.map { case e: EndpointExpr[G] => e }

    def yes: Statement[G] = branch().branches.head._2
    def no: Option[Statement[G]] = Try(branch().branches(1)).toOption.map(_._2)

    // Choreographic branches are unfolded early on, so we only consider the head condition
    def hasUnpointed: Boolean =
      guards.exists {
        case _: EndpointExpr[G] => false
        case _ => true
      }

    def explicitEndpoints: Seq[Endpoint[G]] =
      guards.collect { case EndpointExpr(Ref(endpoint), _) => endpoint }
  }

  object loop {
    def apply(): Loop[G] = inner.asInstanceOf[Loop[G]]

    def guards: Seq[Expr[G]] = AstBuildHelpers.unfoldStar(loop().cond)
    def endpointGuards: Seq[EndpointExpr[G]] =
      guards.map { case e: EndpointExpr[G] => e }

    def hasUnpointed: Boolean =
      guards.exists {
        case _: EndpointExpr[G] => false
        case _ => true
      }

    def explicitEndpoints: Seq[Endpoint[G]] =
      guards.collect { case EndpointExpr(Ref(endpoint), _) => endpoint }
  }

  def participants: Set[Endpoint[G]] =
    ListSet.from(collect {
      case comm: Communicate[G] => comm.participants
      case EndpointStatement(Some(Ref(endpoint)), Assign(_, _)) => Seq(endpoint)
      case c @ ChorStatement(_: Branch[G]) => c.branch.explicitEndpoints
      case c @ ChorStatement(_: Loop[G]) => c.loop.explicitEndpoints
    }.flatten)
}

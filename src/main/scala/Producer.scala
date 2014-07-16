/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter}
import interfaces.{Failure, Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import state.terms._
import silicon.state.{DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import reporting.{DefaultContext, Bookkeeper}
import heap.QuantifiedChunkHelper

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    extends Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext]
        with HasLocalState
    { this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext]
                    with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext]
                    with Brancher[ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type P = DefaultFractionalPermissions

  protected val decider: Decider[P, ST, H, PC, S, C]
  import decider.{fresh, assume}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val bookkeeper: Bookkeeper
  protected val config: Config

  private var snapshotCacheFrames: Stack[Map[Term, (Term, Term)]] = Stack()
  private var snapshotCache: Map[Term, (Term, Term)] = Map()

  def produce(σ: S,
              sf: Sort => Term,
              p: P,
              φ: ast.Expression,
              pve: PartialVerificationError,
              c: C)
             (Q: (S, C) => VerificationResult)
             : VerificationResult =

    produce2(σ, sf, p, φ.whenInhaling, pve, c)((h, c1) =>
      Q(σ \ h, c1))

  def produces(σ: S,
               sf: Sort => Term,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, C) => VerificationResult)
              : VerificationResult =

    if (φs.isEmpty)
      Q(σ, c)
    else {
      val φ = φs.head.whenInhaling
      produce(σ, sf, p, φ, pvef(φ), c)((σ1, c1) =>
        produces(σ1, sf, p, φs.tail, pvef, c1)(Q))
    }

  private def produce2(σ: S,
                       sf: Sort => Term,
                       p: P,
                       φ: ast.Expression,
                       pve: PartialVerificationError,
                       c: C)
                      (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    internalProduce(σ, sf, p, φ, pve, c)((h, c1) => {
      Q(h, c1)
    })
  }

  private def internalProduce(σ: S,
                              sf: Sort => Term,
                              p: P,
                              φ: ast.Expression,
                              pve: PartialVerificationError,
                              c: C)
                             (Q: (H, C) => VerificationResult)
                             : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nPRODUCE ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
    }

    val produced = φ match {
      case ast.And(a0, a1) if !φ.isPure =>
//        println("\n[producer/and]")
//        println(s"  φ = $φ")
        val s0 = mkSnap(a0, c)
        val s1 = mkSnap(a1, c)

        val s0a = s0 // s0.sort match {case _: sorts.Arrow => Select(s0, *()) case _ => s0} /* [SNAP-EQ] */
//        println(s"  s0a = $s0a  (${s0a.sort}, ${s0a.getClass.getSimpleName}})")
        val s1a = s1 // s1.sort match {case _: sorts.Arrow => Select(s1, *()) case _ => s1} /* [SNAP-EQ] */
//        println(s"  s1a = $s1a  (${s1a.sort}, ${s1a.getClass.getSimpleName}})")

        val tSnapEq = Eq(sf(sorts.Snap), Combine(s0a, s1a))
//        println(s"  tSnapEq = $tSnapEq")

        val sf0 = (sort: Sort) => s0.convert(sort)
//        println(s"  sf0 = $sf0")
        val sf1 = (sort: Sort) => s1.convert(sort)
//        println(s"  sf1 = $sf1")

        assume(tSnapEq)
        produce2(σ, sf0, p, a0, pve, c)((h1, c1) =>
          produce2(σ \ h1, sf1, p, a1, pve, c1)((h2, c2) =>
            Q(h2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a0, pve, c2)(Q),
            (c2: C) => Q(σ.h, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a1, pve, c2)(Q),
            (c2: C) => produce2(σ, sf, p, a2, pve, c2)(Q)))

      /* Produce a field access if the heap is quantified for that field */
      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) if quantifiedChunkHelper.isQuantifiedFor(σ.h, field.name) =>
        val ch = quantifiedChunkHelper.getQuantifiedChunk(σ.h, field.name).get // TODO: Slightly inefficient, since it repeats the work of isQuantifiedFor
        eval(σ, eRcvr, pve, c)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val (ch1, _) = quantifiedChunkHelper.transformElement(tRcvr, field.name, s, pNettoGain/*, ch.quantifiedVars*/)
                // TODO: Why is this transform necessary? We already have a quantified chunk ch.
                //       Looking at transformElement I'd say that the call is not needed and that
                //       we can replace ch in σ.h with (ch + pNettoGain), instead of adding ch1 to σ.h.
            assume(NoPerm() < pGain)
            Q(σ.h + ch1, c2)})})

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
            assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)})})

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), gain) =>
        val predicate = c.program.findPredicate(predicateName)
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
          evalp(σ, gain, pve, c1)((pGain, c2) => {
//            println("\n[producer/pred]")
//            println(s"  φ = $φ")
            val s = sf(getOptimalSnapshotSort(predicate.body, c)._1)
//            println(s"  s = $s  (${s.sort}, ${s.getClass.getSimpleName}})")
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)}))

      /* Quantified field access predicate */
      case fa@ ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, f), gain))) =>
        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ((vars map (v => ast.LocalVariable(v.name)(v.typ))) zip tVars)
        val πPre = decider.π
        var πAux: Set[Term] = Set()

this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars = tVars ++: this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars

        decider.locally[(Term, Term, P, C)](QB => {
          decider.prover.logComment("Begin local evaluation of sub-expressions of " + fa)
          eval(σ \+ γVars, cond, pve, c)((tCond, c1) =>
            eval(σ \+ γVars, eRcvr, pve, c1)((tRcvr, c2) =>
              evalp(σ \+ γVars, gain, pve, c2)((pGain, c3) => {
                πAux = decider.π -- πPre
                decider.prover.logComment("End local evaluation of sub-expressions of " + fa)
                QB(tCond, tRcvr, pGain, c3)})))}
    ){case (tCond, tRcvr, pGain, c3) =>
        val tAuxQuant = Quantification(Forall, tVars, state.terms.utils.BigAnd(πAux))
        decider.assume(tAuxQuant)

this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars = this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars.drop(tVars.length)

//                val s = sf(sorts.Arrow(sorts.Ref, toSort(f.typ)))
                val s = sf(sorts.Array(sorts.Ref, toSort(f.typ)))
//                val s = sf(toSort(f.typ))
//                println("\n[produce/forall]")
//                println(s"  s = $s  (${s.sort}, ${s.getClass.getSimpleName}})")
                // val fs = DomainFApp(Function(s.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
//                val fs = App(s, *())
                val fs = Select(s, *())
//                println(s"  fs == $fs  (${fs.sort}}, ${fs.getClass.getSimpleName}})")
//                val ch = quantifiedChunkHelper.transform(tRcvr, f, fs, pGain * p, tCond)
        val ch = quantifiedChunkHelper.transform(tRcvr, f, fs/*sf(toSort(f.typ))*/, pGain * p, tCond, tVars)
//                println(s"  ch = $ch")
        val v = Var("nonnull", sorts.Ref)
        val tNonNullQuant =
          Quantification(
            Forall,
            List(v),
            Implies(
              Less(NoPerm(), ch.perm.replace(*(), v)),
              v !== Null()),
            List(Trigger(List(NullTrigger(v)))))
        assume(Set[Term](NoPerm() < pGain, tNonNullQuant))
        val h =
          if(quantifiedChunkHelper.isQuantifiedFor(σ.h,f.name)) σ.h
          else quantifiedChunkHelper.quantifyChunksForField(σ.h, f.name/*, tVars*/)
        Q(h + ch, c3)}

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(φ))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        eval(σ, φ, pve, c)((t, c1) => {
          assume(t)
          Q(σ.h, c1)})
    }

    produced
  }

  private def getOptimalSnapshotSort(φ: ast.Expression, c: C): (Sort, Boolean) = φ match {
    case _ if φ.isPure =>
      (sorts.Snap, true)

    case ast.AccessPredicate(locacc, _) => locacc match {
      case fa: ast.FieldAccess => (toSort(fa.field.typ), false)
      case pa: ast.PredicateAccess => getOptimalSnapshotSort(c.program.findPredicate(pa.predicateName).body, c)
      /* TODO: Most likely won't terminate for a predicate that only contains
       *       itself in its body, e.g., predicate P(x) {P(x)}.
       */
    }

    case ast.Implies(e0, φ1) =>
      /* φ1 must be impure, otherwise the first case would have applied. */
      getOptimalSnapshotSort(φ1, c)

    case ast.And(φ1, φ2) =>
      /* At least one of φ1, φ2 must be impure, otherwise ... */
      (sorts.Snap, false)
//      getOptimalSnapshotSortFromPair(φ1, φ2, () => (sorts.Snap, false))

    case ast.Ite(_, φ1, φ2) =>
      /* At least one of φ1, φ2 must be impure, otherwise ... */

      def findCommonSort() = {
        val (s1, isPure1) = getOptimalSnapshotSort(φ1, c)
        val (s2, isPure2) = getOptimalSnapshotSort(φ2, c)
        val s = if (s1 == s2) s1 else sorts.Snap
        val isPure = isPure1 && isPure2
        (s, isPure)
      }

      getOptimalSnapshotSortFromPair(φ1, φ2, findCommonSort, c)

    case ast.Forall(_, _, ast.Implies(_, ast.FieldAccessPredicate(ast.FieldAccess(_, f), _))) =>
      /* TODO: This is just a temporary work-around to cope with problems related to quantified permissions. */
//      (toSort(f.typ), false)
//      (sorts.Arrow(sorts.Ref, toSort(f.typ)), false)
      (sorts.Array(sorts.Ref, toSort(f.typ)), false)

    case _ =>
      (sorts.Snap, false)
  }

  private def getOptimalSnapshotSortFromPair(φ1: ast.Expression,
                                             φ2: ast.Expression,
                                             fIfBothImpure: () => (Sort, Boolean),
                                             c: C)
                                            : (Sort, Boolean) = {

    def followImpureIfNotAnd(φ: ast.Expression): (Sort, Boolean) = φ match {
      case _: ast.And => (sorts.Snap, false)
      case _ => getOptimalSnapshotSort(φ, c)
    }

    if (φ1.isPure && !φ2.isPure) followImpureIfNotAnd(φ2)
    else if (!φ1.isPure && φ2.isPure) followImpureIfNotAnd(φ1)
    else fIfBothImpure()
  }

  private def mkSnap(φ: ast.Expression, c: C): Term = {
    val oss = getOptimalSnapshotSort(φ, c)
//    println("\n[mkSnap]")
//    println(s"  φ = $φ")
//    println(s"  oss = $oss  (${oss.getClass.getSimpleName}})")
    val t = oss match {
      case (sorts.Snap, true) => Unit
      //    case (arrow: sorts.Arrow, _) => App(fresh(arrow), *())
      case (sort, _) => fresh(sort)
    }
//    println(s"  t = $t  (${t.sort}, ${t.getClass.getSimpleName}})")
    t
  }

  override def pushLocalState() {
    snapshotCacheFrames = snapshotCache :: snapshotCacheFrames
    super.pushLocalState()
  }

  override def popLocalState() {
    snapshotCache = snapshotCacheFrames.head
    snapshotCacheFrames = snapshotCacheFrames.tail
    super.popLocalState()
  }
}

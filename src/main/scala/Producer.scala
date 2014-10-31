/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, Chunk, StateFactory}
import interfaces.{Success, Failure, Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import state.terms._
import state.{DirectChunk, DefaultContext, MagicWandChunk, DirectFieldChunk, DirectPredicateChunk, SymbolConvert}
import reporting.Bookkeeper
import supporters.MagicWandSupporter

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    extends Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[H]]
       with HasLocalState
    { this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[H]]
                    with Consumer[DefaultFractionalPermissions, Chunk, ST, H, S, DefaultContext[H]]
                    with Brancher[ST, H, S, DefaultContext[H]]
                    with MagicWandSupporter[ST, H, PC, S] =>

  private type C = DefaultContext[H]
  private type P = DefaultFractionalPermissions

  protected val decider: Decider[P, ST, H, PC, S, C]
  import decider.{fresh, assume}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

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
              : VerificationResult = {

    /* TODO: produces(φs) allows more fine-grained error reporting when compared
     *       to produce(BigAnd(φs)) because with produces, each φ in φs can be
     *       produced with its own PartialVerificationError.
     *       The two differ in behaviour, though, because producing a list of,
     *       e.g., preconditions, with produce results in more explicit
     *       conjunctions, and thus in more combine-terms.
     *       It is therefore necessary to duplicate the code from producing
     *       conjunctions (ast.And) that records snapshots in order to ensure
     *       that both produce and produces create the same location-to-snapshot
     *       mappings.
     *       It would obviously be better if we could avoid the code duplication
     *       while preserving the ability of generating more fine-grained errors.
     */

    if (φs.isEmpty)
      Q(σ, c)
    else {
      val φ = φs.head.whenInhaling

      if (φs.tail.isEmpty)
        produce(σ, sf, p, φ, pvef(φ), c)(Q)
      else {
        val (c1, rootSnap) = c.snapshotRecorder match {
          case Some(sr) =>
            val rootSnap = sr.currentSnap
            (c.copy(snapshotRecorder = Some(sr.copy(currentSnap = First(sr.currentSnap)))), rootSnap)
          case _ =>
            (c, null)}

        produce(σ, sf, p, φ, pvef(φ), c1)((σ1, c2) => {
          val c3 = c2.snapshotRecorder match {
            case Some(sr) => c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Second(rootSnap))))
            case _ => c2}
          produces(σ1, sf, p, φs.tail, pvef, c3)(Q)})
      }
    }
  }

  private def produce2(σ: S,
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
        val s = sf(sorts.Snap)
        val s0 = mkSnap(a0, c.program)
        val s1 = mkSnap(a1, c.program)

        assume(s === Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

        val (c1, rootSnap) = c.snapshotRecorder match {
          case Some(sr) =>
            val rootSnap = sr.currentSnap
            (c.copy(snapshotRecorder = Some(sr.copy(currentSnap = First(sr.currentSnap)))), rootSnap)
          case _ =>
            (c, null)}

        produce2(σ, sf0, p, a0, pve, c1)((h1, c2) => {
          val c3 = c2.snapshotRecorder match {
            case Some(sr) => c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Second(rootSnap))))
            case _ => c2}
          produce2(σ \ h1, sf1, p, a1, pve, c3)((h2, c4) =>
            Q(h2, c4))})

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

      case acc @ ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          /* Assuming receiver non-null might contradict current path conditions
           * and we would like to detect that as early as possible.
           * We could try to assert false after the assumption, but it seems likely
           * that 'tRcvr === Null()' syntactically occurs in the path conditions if
           * it is true. Hence, we assert it here, which (should) syntactically look
           * for the term before calling Z3.
           */
          if (decider.check(σ, tRcvr === Null())) /* TODO: Benchmark performance impact */
            Success()
          else {
            assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1)((pGain, c2) => {
            assume(NoPerm() < pGain)
              val s = sf(toSort(field.typ))
              val pNettoGain = pGain * p
              val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
            val (h1, matchedChunk, t) = addDirectChunk(σ.h, ch)
            assume(t)
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = sr.copy(chunkToSnap = sr.chunkToSnap + (matchedChunk.getOrElse(ch).id -> sr.currentSnap))
                c2.copy(snapshotRecorder = Some(sr1))
              case _ => c2}
            Q(h1, c3)})})

      case acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), gain) =>
        val predicate = c.program.findPredicate(predicateName)
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
          evalp(σ, gain, pve, c1)((pGain, c2) => {
            assume(NoPerm() < pGain)
            val s = sf(getOptimalSnapshotSort(predicate.body, c.program)._1)
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            val (h1, matchedChunk, t) = addDirectChunk(σ.h, ch)
            assume(t)
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = sr.copy(chunkToSnap = sr.chunkToSnap + (matchedChunk.getOrElse(ch).id -> sr.currentSnap))
                c2.copy(snapshotRecorder = Some(sr1))
              case _ => c2}
            Q(h1, c3)}))

      case wand: ast.MagicWand =>
        println("\n[Producer/MagicWand]")
        println(s"  wand = $wand")
        // val ch = magicWandSupporter.createChunk(σ.γ, /*σ.h,*/ wand)
        // eval(σ, wand, pve, c)((tWand, c1) => {
        magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) => {
          println(s"  chWand = $chWand")
          Q(σ.h + chWand, c)})

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

  private def getOptimalSnapshotSort(φ: ast.Expression, program: ast.Program, visited: Seq[String] = Nil)
                                    : (Sort, Boolean) =

    φ match {
      case _ if φ.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(locacc, _) => locacc match {
        case fa: ast.FieldAccess =>
          (toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName))
            getOptimalSnapshotSort(program.findPredicate(pa.predicateName).body, program, pa.predicateName +: visited)
          else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (sorts.Snap, false)
      }

      case ast.Implies(e0, φ1) =>
        /* φ1 must be impure, otherwise the first case would have applied. */
        getOptimalSnapshotSort(φ1, program, visited)

      case ast.And(φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(φ1, φ2, () => (sorts.Snap, false), program, visited)

      case ast.Ite(_, φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = getOptimalSnapshotSort(φ1, program, visited)
          val (s2, isPure2) = getOptimalSnapshotSort(φ2, program, visited)
          val s = if (s1 == s2) s1 else sorts.Snap
          val isPure = isPure1 && isPure2
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(φ1, φ2, findCommonSort, program, visited)

      case ast.Forall(_, _, ast.Implies(_, ast.FieldAccessPredicate(ast.FieldAccess(_, f), _))) =>
        /* TODO: This is just a temporary work-around to cope with problems related to quantified permissions. */
        (toSort(f.typ), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(φ1: ast.Expression,
                                             φ2: ast.Expression,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: Seq[String])
                                            : (Sort, Boolean) = {

    if (φ1.isPure && !φ2.isPure) getOptimalSnapshotSort(φ2, program, visited)
    else if (!φ1.isPure && φ2.isPure) getOptimalSnapshotSort(φ1, program, visited)
    else fIfBothPure()
  }

  private def mkSnap(φ: ast.Expression, program: ast.Program, visited: Seq[String] = Nil): Term =
    getOptimalSnapshotSort(φ, program, visited) match {
      case (sorts.Snap, true) => Unit
      case (sort, _) => fresh(sort)
    }

  private def addDirectChunk(h: H, dc: DirectChunk): (H, Option[DirectChunk], Term) = {
    var matchingChunk: Option[DirectChunk] = None
    var tEq: Term = True()

    /* Only the first match will be considered. This is incomplete, but sound,
     * and the underlying assumption is that the input heap is "tidy" in the
     * sense that there will be at most one chunk that syntactically matches
     * the given chunk dc.
     */

    /* TODO: Code duplication is necessary because a FieldChunk has a value
     *       whereas a predicate chunk has a snap(shot).
     *       The two should be unified (as VeriFast does).
     */
    val chunks = h.values.map {
      case ch: DirectFieldChunk if matchingChunk.isEmpty && ch.name == dc.name && ch.args == dc.args =>
        tEq = ch.value === dc.asInstanceOf[DirectFieldChunk].value
        matchingChunk = Some(ch)

        ch + dc.perm

      case ch: DirectPredicateChunk if matchingChunk.isEmpty && ch.name == dc.name && ch.args == dc.args =>
        tEq = ch.snap === dc.asInstanceOf[DirectPredicateChunk].snap
        matchingChunk = Some(ch)

        ch + dc.perm

      case ch => ch
    }

    val h1 =
      if (matchingChunk.nonEmpty) H(chunks)
      else H(chunks) + dc

    (h1, matchingChunk, tEq)
  }

  override def pushLocalState() {
    snapshotCacheFrames = snapshotCache +: snapshotCacheFrames
    super.pushLocalState()
  }

  override def popLocalState() {
    snapshotCache = snapshotCacheFrames.head
    snapshotCacheFrames = snapshotCacheFrames.tail
    super.popLocalState()
  }
}

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutesComputability
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoiceComputability
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.RetainedAngularFanSourceEscapedSpliceComputability

/-!
# Computability of final coordinated retained routes

The final retained router combines a source-scaled angular occurrence order,
one of the finite coordinated direct-route choices, and the unchanged Figure 7
occurrence suffix.  This file first proves the shared scaled slot and suffix
computable, then assembles the direct, escaped-fallback, and total route
branches.  It finally computes the normalized orthogonal route and the first
direction used by the downstream clockwise clause ordering.
-/

noncomputable section

namespace LeanTrominoes

set_option maxHeartbeats 500000

/-- Uniform scaling of all points in a finite polyline is primitive
recursive. -/
theorem scalePolyline_primrec : Primrec₂ scalePolyline := by
  change Primrec fun input : Int × List Cell =>
    scalePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_scale_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Bounding an arbitrary natural index to one of the eight terminal slots
is primitive recursive. -/
theorem boundedRetainedTerminalSlot_primrec :
    Primrec boundedRetainedTerminalSlot := by
  let boundedPred : PrimrecPred fun index : Nat => index < 8 :=
    Primrec.nat_lt.comp Primrec.id (Primrec.const 8)
  let Bounded := { index : Nat // index < 8 }
  letI : Primcodable Bounded := Primcodable.subtype boundedPred
  have reduced : Primrec fun index : Nat => min index 7 :=
    Primrec.nat_min.comp Primrec.id (Primrec.const 7)
  have bounded : Primrec fun index : Nat =>
      (⟨min index 7, by omega⟩ : Bounded) :=
    Primrec.subtype_mk (hp := boundedPred) reduced
  have convert : Primrec (Fin.equivSubtype (n := 8)).symm :=
    Primrec.of_equiv_symm
  exact (convert.comp bounded).of_eq fun _ => rfl

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open OccurrenceSplitRing

/-! ## Final fallback branch metadata -/

namespace PositionedPeriodicClause

/-- Scaling one positioned clause by a fixed natural factor is primitive
recursive. -/
theorem scale_primrec
    {Variable : Type*} [Primcodable Variable]
    (factor : Nat) :
    Primrec (PositionedPeriodicClause.scale factor :
      PositionedPeriodicClause Variable → _) := by
  have position : Primrec fun clause : PositionedPeriodicClause Variable =>
      Cell.scale factor clause.position :=
    Computability.cell_scale_primrec.comp
      (Primrec.const (factor : Int))
      PositionedPeriodicClause.position_primrec
  exact (PositionedPeriodicClause.mk_primrec.comp
    (Primrec.pair position
      PositionedPeriodicClause.literals_primrec)).of_eq fun _ => rfl

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

/-- Scaling every clause position in a finite positioned formula by a fixed
natural factor is primitive recursive. -/
theorem scale_primrec
    {Variable : Type*} [Primcodable Variable]
    (factor : Nat) :
    Primrec (PositionedPeriodicCNF.scale factor :
      PositionedPeriodicCNF Variable → _) := by
  have scaledClauses : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.map (PositionedPeriodicClause.scale factor) :=
    Primrec.list_map PositionedPeriodicCNF.clauses_primrec
      ((PositionedPeriodicClause.scale_primrec factor).comp Primrec.snd).to₂
  exact (PositionedPeriodicCNF.mk_primrec.comp scaledClauses).of_eq
    fun _ => rfl

end PositionedPeriodicCNF

private abbrev FinalCoordinatedVariable (Variable : Type*) :=
  WrappedPeriodicPlanarSATVariable Variable

private def finalCoordinatedScaledSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF (FinalCoordinatedVariable Variable) :=
  (finalCoordinatedSource formula).scale
    retainedAngularFanSourceClearanceFactor

private def finalCoordinatedScaledPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement (FinalCoordinatedVariable Variable) :=
  (finalCoordinatedPlacement formula).scale
    retainedAngularFanSourceClearanceFactor

private def finalCoordinatedScaledOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    OccurrenceOrder (finalCoordinatedScaledSource formula).erase :=
  angularOccurrenceOrder
    (finalCoordinatedScaledSource formula).erase
    (PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula))

private theorem finalCoordinatedScaledOrder_copies_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : FinalCoordinatedVariable Variable) :
    (finalCoordinatedScaledOrder formula).copies atom =
      (retainedDrawingAngularOccurrenceOrder formula).copies atom := by
  unfold finalCoordinatedScaledOrder finalCoordinatedScaledSource
    finalCoordinatedSource finalCoordinatedSourceRoutes
    retainedDrawingAngularOccurrenceOrder retainedPlanarSATFormula
  simpa only [PositionedPeriodicCNF.erase_scale] using
    retainedAngularFanSourceScaled_angularOccurrenceOrder
      retainedAngularFanSourceClearanceFactor_pos
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      atom

private theorem retainedFinalCoordinatedOccurrenceSlot_eq_unscaled
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PeriodicLiteral (FinalCoordinatedVariable Variable))
    (clauseIndex literalIndex : Nat) :
    retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex =
      boundedRetainedTerminalSlot
        (angularOccurrenceIndex
          (retainedDrawingAngularOccurrenceOrder formula)
          literal clauseIndex literalIndex) := by
  unfold retainedFinalCoordinatedOccurrenceSlot
    finalCoordinatedSource finalCoordinatedSourceRoutes
    retainedDrawingAngularOccurrenceOrder retainedPlanarSATFormula
    angularOccurrenceIndex
  dsimp only
  rw [retainedAngularFanSourceScaled_angularOccurrenceOrder
    retainedAngularFanSourceClearanceFactor_pos
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    literal.atom]

private theorem finalCoordinatedScaledOrder_copies_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        FinalCoordinatedVariable Variable =>
      (finalCoordinatedScaledOrder input.1).copies input.2 := by
  exact (retainedDrawingAngularOccurrenceOrder_copies_primrec
    (Variable := Variable)).of_eq fun input =>
      (finalCoordinatedScaledOrder_copies_eq input.1 input.2).symm

private theorem finalCoordinatedScaledPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun formula : PeriodicCNF Variable =>
      (finalCoordinatedScaledPlacement formula).period := by
  unfold finalCoordinatedScaledPlacement finalCoordinatedPlacement
  exact Primrec.nat_mul.comp
    (Primrec.const retainedAngularFanSourceClearanceFactor)
    retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec

private theorem finalCoordinatedScaledPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        FinalCoordinatedVariable Variable =>
      (finalCoordinatedScaledPlacement input.1).position input.2 := by
  unfold finalCoordinatedScaledPlacement finalCoordinatedPlacement
  exact Computability.cell_scale_primrec.comp
    (Primrec.const (retainedAngularFanSourceClearanceFactor : Int))
    retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec

private theorem finalCoordinatedScaledSource_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedScaledSource :
      PeriodicCNF Variable → _) := by
  exact (PositionedPeriodicCNF.scale_primrec
    retainedAngularFanSourceClearanceFactor).comp
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec

abbrev RetainedFinalFallbackQuery (Variable : Type*) :=
  (PeriodicCNF Variable × Nat) × Nat

/-- Uncurried singleton-prefix escape test for one final retained route. -/
def retainedFinalFallbackUsesEscapeQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : Bool :=
  retainedFinalFallbackUsesEscape input.1.1 input.1.2 input.2

/-- The exceptional escaped-fallback test is primitive recursive.  Its
`dropLast` has length one exactly when the original route has length two. -/
theorem retainedFinalFallbackUsesEscapeQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalFallbackUsesEscapeQuery
      (Variable := Variable)) := by
  let Query := RetainedFinalFallbackQuery Variable
  have route : Primrec fun input : Query =>
      finalCoordinatedSourceRoutes input.1.1 input.1.2 input.2 := by
    unfold finalCoordinatedSourceRoutes
    exact retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec
  have length : Primrec fun input : Query =>
      (finalCoordinatedSourceRoutes
        input.1.1 input.1.2 input.2).length :=
    Primrec.list_length.comp route
  have lengthTwo : PrimrecPred fun input : Query =>
      (finalCoordinatedSourceRoutes
        input.1.1 input.1.2 input.2).length = 2 :=
    Primrec.eq.comp length (Primrec.const 2)
  exact lengthTwo.decide.of_eq fun input => by
    unfold retainedFinalFallbackUsesEscapeQuery
      retainedFinalFallbackUsesEscape
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [List.length_dropLast]
    omega

abbrev FinalCoordinatedScaledClauseQuery (Variable : Type*) :=
  PeriodicCNF Variable × Nat

/-- Uncurried scaled-source clause lookup used by both final route branches. -/
def finalCoordinatedScaledClauseQuery?
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedScaledClauseQuery Variable) :=
  finalCoordinatedScaledClause? input.1 input.2

/-- The exact scaled-source clause lookup is primitive recursive. -/
theorem finalCoordinatedScaledClauseQuery?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedScaledClauseQuery?
      (Variable := Variable)) := by
  have clauses : Primrec fun input :
      FinalCoordinatedScaledClauseQuery Variable =>
      (finalCoordinatedScaledSource input.1).clauses :=
    PositionedPeriodicCNF.clauses_primrec.comp
      (finalCoordinatedScaledSource_primrec.comp Primrec.fst)
  exact (Primrec.list_getElem?.comp clauses Primrec.snd).of_eq
    fun _ => rfl

private abbrev FinalCoordinatedSuffixQuery (Variable : Type*) :=
  (((PeriodicCNF Variable ×
      AngularClauseRouteData (FinalCoordinatedVariable Variable)) ×
    AngularLiteralRouteData (FinalCoordinatedVariable Variable)) × Nat) × Nat

abbrev RetainedFinalCoordinatedOccurrenceSlotQuery (Variable : Type*) :=
  FinalCoordinatedSuffixQuery Variable

private abbrev FinalCoordinatedActualOccurrenceQuery (Variable : Type*) :=
  (((PeriodicCNF Variable ×
      PositionedPeriodicClause (FinalCoordinatedVariable Variable)) ×
    PeriodicLiteral (FinalCoordinatedVariable Variable)) × Nat) × Nat

private theorem finalCoordinatedUnscaledOccurrenceIndex_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : FinalCoordinatedActualOccurrenceQuery Variable =>
      angularOccurrenceIndex
        (retainedDrawingAngularOccurrenceOrder input.1.1.1.1)
        input.1.1.2 input.1.2 input.2 :=
  angularOccurrenceIndex_primrec
    (fun formula atom =>
      (retainedDrawingAngularOccurrenceOrder formula).copies atom)
    retainedDrawingAngularOccurrenceOrder_copies_primrec

private theorem finalCoordinatedOccurrence_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (item : ThreeOccurrenceVariable Variable)
    (items : List (ThreeOccurrenceVariable Variable)) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq item items = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

private def finalCoordinatedFlatUnscaledOccurrenceIndex
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) : Nat :=
  (angularOccurrenceVariables
      (retainedPlanarSATFormula input.1.1.1.1)
      (finalCoordinatedSourceRoutes input.1.1.1.1)
      input.1.1.2.1).idxOf
    (input.1.1.2.1, input.1.2, input.2)

private theorem finalCoordinatedAngularOccurrenceVariables_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        FinalCoordinatedVariable Variable =>
      angularOccurrenceVariables
        (retainedPlanarSATFormula input.1)
        (finalCoordinatedSourceRoutes input.1) input.2 := by
  unfold finalCoordinatedSourceRoutes
  exact angularOccurrenceVariables_primrec
    retainedPlanarSATFormula
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    retainedPlanarSATFormula_primrec
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec

private def finalCoordinatedFlatCopies
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) :
    List (ThreeOccurrenceVariable (FinalCoordinatedVariable Variable)) :=
  angularOccurrenceVariables
    (retainedPlanarSATFormula input.1.1.1.1)
    (finalCoordinatedSourceRoutes input.1.1.1.1)
    input.1.1.2.1

private theorem finalCoordinatedFlatCopies_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedFlatCopies (Variable := Variable)) := by
  have query : Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      (input.1.1.1.1, input.1.1.2.1) :=
    Primrec.pair
      (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  exact (finalCoordinatedAngularOccurrenceVariables_primrec.comp
    query).of_eq fun _ => rfl

private theorem finalCoordinatedFlatOccurrence_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      (input.1.1.2.1, input.1.2, input.2) := by
  have atom : Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      input.1.1.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.pair atom
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

private theorem finalCoordinatedFlatUnscaledOccurrenceIndex_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedFlatUnscaledOccurrenceIndex
      (Variable := Variable)) := by
  let Query := FinalCoordinatedSuffixQuery Variable
  have items : Primrec fun input : Query =>
      angularOccurrenceVariables
        (retainedPlanarSATFormula input.1.1.1.1)
        (finalCoordinatedSourceRoutes input.1.1.1.1)
        input.1.1.2.1 :=
    finalCoordinatedFlatCopies_primrec.of_eq fun _ => rfl
  have occurrence : Primrec fun input : Query =>
      (input.1.1.2.1, input.1.2, input.2) :=
    finalCoordinatedFlatOccurrence_primrec
  exact (Primrec.list_idxOf.comp occurrence items).of_eq fun input =>
    finalCoordinatedOccurrence_idxOf_decidableEq_eq
      (indexedOccurrence (angularLiteralOfRouteData input.1.1.2)
        input.1.2 input.2)
      (angularOccurrenceVariables
        (retainedPlanarSATFormula input.1.1.1.1)
        (finalCoordinatedSourceRoutes input.1.1.1.1)
        input.1.1.2.1)

/-- Uncurried exact occurrence-slot query used by the final coordinated
router. -/
def retainedFinalCoordinatedOccurrenceSlotQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedOccurrenceSlotQuery Variable) :
    RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot
    input.1.1.1.1 (angularLiteralOfRouteData input.1.1.2)
    input.1.2 input.2

/-- The exact source-scaled occurrence-slot query is primitive recursive. -/
theorem retainedFinalCoordinatedOccurrenceSlotQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalCoordinatedOccurrenceSlotQuery
      (Variable := Variable)) := by
  let Query := RetainedFinalCoordinatedOccurrenceSlotQuery Variable
  have computed : Primrec fun input : Query =>
      boundedRetainedTerminalSlot
        (finalCoordinatedFlatUnscaledOccurrenceIndex input) :=
    boundedRetainedTerminalSlot_primrec.comp
      finalCoordinatedFlatUnscaledOccurrenceIndex_primrec
  exact computed.of_eq fun input =>
    by
      unfold retainedFinalCoordinatedOccurrenceSlotQuery
      rw [retainedFinalCoordinatedOccurrenceSlot_eq_unscaled]
      rfl

private theorem retainedFinalCoordinatedOccurrenceSlot_query_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      retainedFinalCoordinatedOccurrenceSlot
        input.1.1.1.1 (angularLiteralOfRouteData input.1.1.2)
        input.1.2 input.2 :=
  retainedFinalCoordinatedOccurrenceSlotQuery_primrec

private def finalCoordinatedFlatRelativeOffset
    {Variable : Type*}
    (input : FinalCoordinatedSuffixQuery Variable) : Cell :=
  incidenceRelativeOffset
    (angularClauseOfRouteData input.1.1.1.2)
    (angularLiteralOfRouteData input.1.1.2)

private theorem finalCoordinatedFlatRelativeOffset_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedFlatRelativeOffset
      (Variable := Variable)) := by
  have clauseData : Primrec fun input :
      FinalCoordinatedSuffixQuery Variable => input.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have literalData : Primrec fun input :
      FinalCoordinatedSuffixQuery Variable => input.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact (incidenceRelativeOffset_primrec.comp
    (Primrec.pair
      (angularClauseOfRouteData_primrec.comp clauseData)
      (angularLiteralOfRouteData_primrec.comp literalData))).of_eq
        fun _ => rfl

private abbrev FinalCoordinatedSpokeQuery (Variable : Type*) :=
  (((PeriodicCNF Variable × FinalCoordinatedVariable Variable) × Cell) × Nat)

private def finalCoordinatedFlatSpokeInput
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) :
    FinalCoordinatedSpokeQuery Variable :=
  (((input.1.1.1.1, input.1.1.2.1),
    finalCoordinatedFlatRelativeOffset input),
    finalCoordinatedFlatUnscaledOccurrenceIndex input)

private theorem finalCoordinatedFlatSpokeInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedFlatSpokeInput
      (Variable := Variable)) := by
  have formula : Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      input.1.1.1.1 :=
    Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have atom : Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      input.1.1.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.pair
    (Primrec.pair (Primrec.pair formula atom)
      finalCoordinatedFlatRelativeOffset_primrec)
    finalCoordinatedFlatUnscaledOccurrenceIndex_primrec).of_eq
      fun _ => rfl

private def finalCoordinatedFlatOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) : List Cell :=
  angularFanSpokeRouteAt
    (finalCoordinatedScaledPlacement input.1.1.1.1)
    input.1.1.2.1
    (finalCoordinatedFlatRelativeOffset input)
    (finalCoordinatedFlatUnscaledOccurrenceIndex input)

private theorem finalCoordinatedFlatOccurrenceSuffix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedFlatOccurrenceSuffix
      (Variable := Variable)) := by
  have spoke : Primrec fun input : FinalCoordinatedSpokeQuery Variable =>
      angularFanSpokeRouteAt
        (finalCoordinatedScaledPlacement input.1.1.1)
        input.1.1.2 input.1.2 input.2 :=
    angularFanSpokeRouteAt_primrec
      finalCoordinatedScaledPlacement
      finalCoordinatedScaledPlacement_period_primrec
      finalCoordinatedScaledPlacement_position_primrec
  exact (spoke.comp finalCoordinatedFlatSpokeInput_primrec).of_eq
    fun _ => rfl

private theorem finalCoordinatedOccurrenceSuffix_eq_flat
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) :
    angularOccurrenceSuffix
        (finalCoordinatedScaledPlacement input.1.1.1.1)
        (finalCoordinatedScaledOrder input.1.1.1.1)
        (angularClauseOfRouteData input.1.1.1.2)
        (angularLiteralOfRouteData input.1.1.2)
        input.1.2 input.2 =
      finalCoordinatedFlatOccurrenceSuffix input := by
  unfold angularOccurrenceSuffix finalCoordinatedFlatOccurrenceSuffix
    finalCoordinatedFlatRelativeOffset
    finalCoordinatedFlatUnscaledOccurrenceIndex angularOccurrenceIndex
  rw [finalCoordinatedScaledOrder_copies_eq]
  rfl

private theorem finalCoordinatedOccurrenceSuffix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : FinalCoordinatedSuffixQuery Variable =>
      angularOccurrenceSuffix
        (finalCoordinatedScaledPlacement input.1.1.1.1)
        (finalCoordinatedScaledOrder input.1.1.1.1)
        (angularClauseOfRouteData input.1.1.1.2)
        (angularLiteralOfRouteData input.1.1.2)
        input.1.2 input.2 := by
  exact finalCoordinatedFlatOccurrenceSuffix_primrec.of_eq fun input =>
    (finalCoordinatedOccurrenceSuffix_eq_flat input).symm

abbrev RetainedFinalCoordinatedDirectRouteQuery (Variable : Type*) :=
  (((((PeriodicCNF Variable × RetainedDirectSourceRouteChoice) ×
      AngularClauseRouteData (FinalCoordinatedVariable Variable)) ×
    AngularLiteralRouteData (FinalCoordinatedVariable Variable)) × Nat) × Nat)

/-- Uncurried successful coordinated direct-route construction. -/
def retainedFinalCoordinatedDirectOccurrenceRouteQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) : List Cell :=
  retainedFinalCoordinatedDirectOccurrenceRoute
    input.1.1.1.1.1 input.1.1.1.1.2
    (angularClauseOfRouteData input.1.1.1.2)
    (angularLiteralOfRouteData input.1.1.2)
    input.1.2 input.2

private def finalCoordinatedDirectSuffixInput
    {Variable : Type*}
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) :
    FinalCoordinatedSuffixQuery Variable :=
  ((((input.1.1.1.1.1, input.1.1.1.2), input.1.1.2),
    input.1.2), input.2)

private theorem finalCoordinatedDirectSuffixInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedDirectSuffixInput
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst))))
          (Primrec.snd.comp
            (Primrec.fst.comp
              (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd

private def finalCoordinatedDirectSlot
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) :
    RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot
    input.1.1.1.1.1 (angularLiteralOfRouteData input.1.1.2)
    input.1.2 input.2

private theorem finalCoordinatedDirectSlot_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedDirectSlot (Variable := Variable)) := by
  exact (retainedFinalCoordinatedOccurrenceSlot_query_primrec.comp
    finalCoordinatedDirectSuffixInput_primrec).of_eq fun _ => rfl

private def finalCoordinatedDirectChoice
    {Variable : Type*}
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) :
    RetainedDirectSourceRouteChoice :=
  input.1.1.1.1.2

private theorem finalCoordinatedDirectChoice_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedDirectChoice (Variable := Variable)) := by
  have first : Primrec fun input :
      RetainedFinalCoordinatedDirectRouteQuery Variable => input.1 :=
    Primrec.fst
  have second : Primrec fun input :
      RetainedFinalCoordinatedDirectRouteQuery Variable => input.1.1 :=
    Primrec.fst.comp first
  have third : Primrec fun input :
      RetainedFinalCoordinatedDirectRouteQuery Variable => input.1.1.1 :=
    Primrec.fst.comp second
  have fourth : Primrec fun input :
      RetainedFinalCoordinatedDirectRouteQuery Variable => input.1.1.1.1 :=
    Primrec.fst.comp third
  exact Primrec.snd.comp fourth

private def finalCoordinatedDirectPrefix
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) : List Cell :=
  (finalCoordinatedDirectChoice input).completeRoute
    (finalCoordinatedDirectSlot input)

private theorem finalCoordinatedDirectPrefix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedDirectPrefix (Variable := Variable)) := by
  exact RetainedDirectSourceRouteChoice.completeRoute_primrec.comp
    finalCoordinatedDirectChoice_primrec
    finalCoordinatedDirectSlot_primrec

private def finalCoordinatedDirectSuffix
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) : List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    (finalCoordinatedFlatOccurrenceSuffix
      (finalCoordinatedDirectSuffixInput input))

private theorem finalCoordinatedDirectSuffix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedDirectSuffix (Variable := Variable)) := by
  exact (scalePolyline_primrec.comp
    (Primrec.const (retainedTerminalFanRoutingRefinement : Int))
    (finalCoordinatedFlatOccurrenceSuffix_primrec.comp
      finalCoordinatedDirectSuffixInput_primrec)).of_eq fun _ => rfl

private def finalCoordinatedDirectRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) : List Cell :=
  joinAtEndpoint
    (finalCoordinatedDirectPrefix input)
    (finalCoordinatedDirectSuffix input)

private theorem finalCoordinatedDirectRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedDirectRouteComputed
      (Variable := Variable)) := by
  exact joinAtEndpoint_primrec _ _
    finalCoordinatedDirectPrefix_primrec
    finalCoordinatedDirectSuffix_primrec

private theorem retainedFinalCoordinatedDirectOccurrenceRouteQuery_eq_computed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedDirectRouteQuery Variable) :
    retainedFinalCoordinatedDirectOccurrenceRouteQuery input =
      finalCoordinatedDirectRouteComputed input := by
  unfold retainedFinalCoordinatedDirectOccurrenceRouteQuery
    retainedFinalCoordinatedDirectOccurrenceRoute
    finalCoordinatedDirectRouteComputed finalCoordinatedDirectPrefix
    finalCoordinatedDirectChoice finalCoordinatedDirectSlot
    finalCoordinatedDirectSuffix
  dsimp only
  have suffixEq :
      angularOccurrenceSuffix
          ((finalCoordinatedPlacement input.1.1.1.1.1).scale
            retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((finalCoordinatedSource input.1.1.1.1.1).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes input.1.1.1.1.1)))
          (angularClauseOfRouteData input.1.1.1.2)
          (angularLiteralOfRouteData input.1.1.2)
          input.1.2 input.2 =
        finalCoordinatedFlatOccurrenceSuffix
          (finalCoordinatedDirectSuffixInput input) := by
    simpa [finalCoordinatedScaledPlacement, finalCoordinatedScaledOrder,
      finalCoordinatedScaledSource,
      finalCoordinatedDirectSuffixInput] using
      (finalCoordinatedOccurrenceSuffix_eq_flat
        (finalCoordinatedDirectSuffixInput input))
  rw [suffixEq]

/-- A successful final coordinated direct-route choice, joined to its exact
source-scaled Figure 7 suffix, is primitive recursive. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalCoordinatedDirectOccurrenceRouteQuery
      (Variable := Variable)) := by
  exact finalCoordinatedDirectRouteComputed_primrec.of_eq fun input =>
    (retainedFinalCoordinatedDirectOccurrenceRouteQuery_eq_computed
      input).symm

/-! ## Escaped fallback occurrence route -/

abbrev RetainedFinalCoordinatedEscapedRouteQuery (Variable : Type*) :=
  FinalCoordinatedSuffixQuery Variable

/-- Uncurried exceptional delayed-lane fallback occurrence route. -/
def retainedFinalEscapedFallbackOccurrenceRouteQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  retainedFinalEscapedFallbackOccurrenceRoute
    input.1.1.1.1
    (angularClauseOfRouteData input.1.1.1.2)
    (angularLiteralOfRouteData input.1.1.2)
    input.1.2 input.2

private def finalCoordinatedEscapedRawRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  finalCoordinatedSourceRoutes input.1.1.1.1 input.1.2 input.2

private theorem finalCoordinatedEscapedRawRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedRawRoute
      (Variable := Variable)) := by
  have route : Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      finalCoordinatedSourceRoutes input.1.1 input.1.2 input.2 := by
    unfold finalCoordinatedSourceRoutes
    exact retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec
  have query : Primrec fun input :
      RetainedFinalCoordinatedEscapedRouteQuery Variable =>
      ((input.1.1.1.1, input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact (route.comp query).of_eq fun _ => rfl

private def finalCoordinatedEscapedRawTerminal
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    RetainedTerminalData :=
  classifiedRetainedTerminalData
    (routeTerminalVector (finalCoordinatedEscapedRawRoute input))

private theorem finalCoordinatedEscapedRawTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedRawTerminal
      (Variable := Variable)) := by
  exact (classifiedRetainedTerminalData_primrec.comp
    (routeTerminalVector_primrec.comp
      finalCoordinatedEscapedRawRoute_primrec)).of_eq fun _ => rfl

private def finalCoordinatedEscapedScaledRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  scalePolyline retainedAngularFanSourceClearanceFactor
    (finalCoordinatedEscapedRawRoute input)

private theorem finalCoordinatedEscapedScaledRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedScaledRoute
      (Variable := Variable)) := by
  exact (scalePolyline_primrec.comp
    (Primrec.const (retainedAngularFanSourceClearanceFactor : Int))
    finalCoordinatedEscapedRawRoute_primrec).of_eq fun _ => rfl

private def finalCoordinatedEscapedScaledTerminal
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    RetainedTerminalData :=
  scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
    (finalCoordinatedEscapedRawTerminal input)

private theorem finalCoordinatedEscapedScaledTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedScaledTerminal
      (Variable := Variable)) := by
  have direction : Primrec fun input :
      RetainedFinalCoordinatedEscapedRouteQuery Variable =>
      (finalCoordinatedEscapedRawTerminal input).1 :=
    Primrec.fst.comp finalCoordinatedEscapedRawTerminal_primrec
  have length : Primrec fun input :
      RetainedFinalCoordinatedEscapedRouteQuery Variable =>
      retainedAngularFanSourceClearanceFactor *
        (finalCoordinatedEscapedRawTerminal input).2 :=
    Primrec.nat_mul.comp
      (Primrec.const retainedAngularFanSourceClearanceFactor)
      (Primrec.snd.comp finalCoordinatedEscapedRawTerminal_primrec)
  exact (Primrec.pair direction length).of_eq fun _ => rfl

private def finalCoordinatedEscapedBoundaryInput
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    RetainedEscapedBoundaryQuery :=
  ((finalCoordinatedEscapedScaledRoute input,
    finalCoordinatedEscapedScaledTerminal input),
    retainedFinalCoordinatedOccurrenceSlot
      input.1.1.1.1 (angularLiteralOfRouteData input.1.1.2)
      input.1.2 input.2)

private theorem finalCoordinatedEscapedBoundaryInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedBoundaryInput
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.pair
      finalCoordinatedEscapedScaledRoute_primrec
      finalCoordinatedEscapedScaledTerminal_primrec)
    retainedFinalCoordinatedOccurrenceSlot_query_primrec

private def finalCoordinatedEscapedPrefix
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  retainedAngularFanEscapedSplicedBoundaryRouteQuery
    (finalCoordinatedEscapedBoundaryInput input)

private theorem finalCoordinatedEscapedPrefix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedPrefix
      (Variable := Variable)) :=
  retainedAngularFanEscapedSplicedBoundaryRouteQuery_primrec.comp
    finalCoordinatedEscapedBoundaryInput_primrec

private def finalCoordinatedEscapedSuffix
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    (finalCoordinatedFlatOccurrenceSuffix input)

private theorem finalCoordinatedEscapedSuffix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedSuffix
      (Variable := Variable)) := by
  exact (scalePolyline_primrec.comp
    (Primrec.const (retainedTerminalFanRoutingRefinement : Int))
    finalCoordinatedFlatOccurrenceSuffix_primrec).of_eq fun _ => rfl

private def finalCoordinatedEscapedRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    List Cell :=
  joinAtEndpoint
    (finalCoordinatedEscapedPrefix input)
    (finalCoordinatedEscapedSuffix input)

private theorem finalCoordinatedEscapedRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedRouteComputed
      (Variable := Variable)) := by
  exact joinAtEndpoint_primrec _ _
    finalCoordinatedEscapedPrefix_primrec
    finalCoordinatedEscapedSuffix_primrec

private theorem retainedFinalEscapedFallbackOccurrenceRouteQuery_eq_computed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedEscapedRouteQuery Variable) :
    retainedFinalEscapedFallbackOccurrenceRouteQuery input =
      finalCoordinatedEscapedRouteComputed input := by
  unfold retainedFinalEscapedFallbackOccurrenceRouteQuery
    retainedFinalEscapedFallbackOccurrenceRoute
    finalCoordinatedEscapedRouteComputed finalCoordinatedEscapedPrefix
    finalCoordinatedEscapedBoundaryInput
    finalCoordinatedEscapedScaledRoute
    finalCoordinatedEscapedScaledTerminal
    finalCoordinatedEscapedRawTerminal
    finalCoordinatedEscapedRawRoute
    finalCoordinatedEscapedSuffix
    retainedAngularFanEscapedSplicedBoundaryRouteQuery
  dsimp only
  have suffixEq :
      angularOccurrenceSuffix
          ((finalCoordinatedPlacement input.1.1.1.1).scale
            retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((finalCoordinatedSource input.1.1.1.1).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes input.1.1.1.1)))
          (angularClauseOfRouteData input.1.1.1.2)
          (angularLiteralOfRouteData input.1.1.2)
          input.1.2 input.2 =
        finalCoordinatedFlatOccurrenceSuffix input := by
    simpa [finalCoordinatedScaledPlacement, finalCoordinatedScaledOrder,
      finalCoordinatedScaledSource] using
      (finalCoordinatedOccurrenceSuffix_eq_flat input)
  rw [suffixEq]

/-- The exceptional delayed-lane fallback occurrence route, including its
unchanged source-scaled Figure 7 suffix, is primitive recursive. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalEscapedFallbackOccurrenceRouteQuery
      (Variable := Variable)) := by
  exact finalCoordinatedEscapedRouteComputed_primrec.of_eq fun input =>
    (retainedFinalEscapedFallbackOccurrenceRouteQuery_eq_computed
      input).symm

/-! ## Ordinary fallback occurrence route -/

private def finalCoordinatedOrdinaryScaledTerminal
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) :
    RetainedTerminalData :=
  classifiedRetainedTerminalData
    (routeTerminalVector (finalCoordinatedEscapedScaledRoute input))

private theorem finalCoordinatedOrdinaryScaledTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedOrdinaryScaledTerminal
      (Variable := Variable)) := by
  exact (classifiedRetainedTerminalData_primrec.comp
    (routeTerminalVector_primrec.comp
      finalCoordinatedEscapedScaledRoute_primrec)).of_eq fun _ => rfl

private def finalCoordinatedOrdinaryBoundaryInput
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) :
    RetainedBoundaryQuery :=
  ((finalCoordinatedEscapedScaledRoute input,
    finalCoordinatedOrdinaryScaledTerminal input),
    retainedFinalCoordinatedOccurrenceSlot
      input.1.1.1.1 (angularLiteralOfRouteData input.1.1.2)
      input.1.2 input.2)

private theorem finalCoordinatedOrdinaryBoundaryInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedOrdinaryBoundaryInput
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.pair
      finalCoordinatedEscapedScaledRoute_primrec
      finalCoordinatedOrdinaryScaledTerminal_primrec)
    retainedFinalCoordinatedOccurrenceSlot_query_primrec

private def finalCoordinatedOrdinaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) : List Cell :=
  retainedAngularFanSplicedBoundaryRouteQuery
    (finalCoordinatedOrdinaryBoundaryInput input)

private theorem finalCoordinatedOrdinaryPrefix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedOrdinaryPrefix
      (Variable := Variable)) :=
  retainedAngularFanSplicedBoundaryRouteQuery_primrec.comp
    finalCoordinatedOrdinaryBoundaryInput_primrec

private def finalCoordinatedOrdinaryRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSuffixQuery Variable) : List Cell :=
  joinAtEndpoint
    (finalCoordinatedOrdinaryPrefix input)
    (finalCoordinatedEscapedSuffix input)

private theorem finalCoordinatedOrdinaryRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedOrdinaryRouteComputed
      (Variable := Variable)) := by
  exact joinAtEndpoint_primrec _ _
    finalCoordinatedOrdinaryPrefix_primrec
    finalCoordinatedEscapedSuffix_primrec

/-! ## Established ordinary/cycle fallback lookup -/

private abbrev FinalCoordinatedSelectedOccurrenceData
    (Variable : Type*) :=
  AngularClauseRouteData (FinalCoordinatedVariable Variable) ×
    AngularLiteralRouteData (FinalCoordinatedVariable Variable)

private def finalCoordinatedSelectedLiteralData?
    {Variable : Type*}
    (input : RetainedFinalFallbackQuery Variable ×
      PositionedPeriodicClause (FinalCoordinatedVariable Variable)) :
    Option (FinalCoordinatedSelectedOccurrenceData Variable) :=
  input.2.literals[input.1.2]?.map fun literal =>
    (angularClauseRouteData input.2, PeriodicLiteral.equivData literal)

private theorem finalCoordinatedSelectedLiteralData?_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedSelectedLiteralData?
      (Variable := Variable)) := by
  let Combined := RetainedFinalFallbackQuery Variable ×
    PositionedPeriodicClause (FinalCoordinatedVariable Variable)
  have selectedLiteral : Primrec fun input : Combined =>
      input.2.literals[input.1.2]? :=
    Primrec.list_getElem?.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have data : Primrec₂ fun (input : Combined)
      (literal : PeriodicLiteral
        (FinalCoordinatedVariable Variable)) =>
      (angularClauseRouteData input.2,
        PeriodicLiteral.equivData literal) := by
    change Primrec fun input : Combined ×
        PeriodicLiteral (FinalCoordinatedVariable Variable) =>
      (angularClauseRouteData input.1.2,
        PeriodicLiteral.equivData input.2)
    exact (Primrec.pair
      (angularClauseRouteData_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      (PeriodicLiteral.equivData_primrec.comp Primrec.snd)).to₂
  exact (Primrec.option_map selectedLiteral data).of_eq fun _ => rfl

private def finalCoordinatedSelectedOccurrenceData?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    Option (FinalCoordinatedSelectedOccurrenceData Variable) :=
  match finalCoordinatedScaledClause? input.1.1 input.1.2 with
  | none => none
  | some clause => finalCoordinatedSelectedLiteralData? (input, clause)

private theorem finalCoordinatedSelectedOccurrenceData?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedOccurrenceData?
      (Variable := Variable)) := by
  let Query := RetainedFinalFallbackQuery Variable
  have selectedClause : Primrec fun input : Query =>
      finalCoordinatedScaledClause? input.1.1 input.1.2 :=
    finalCoordinatedScaledClauseQuery?_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))
  have none : Primrec fun _input : Query =>
      (none : Option (FinalCoordinatedSelectedOccurrenceData Variable)) :=
    Primrec.const none
  have some : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause
        (FinalCoordinatedVariable Variable)) =>
      finalCoordinatedSelectedLiteralData? (input, clause) :=
    finalCoordinatedSelectedLiteralData?_primrec.to₂
  exact (Primrec.option_casesOn selectedClause none some).of_eq
    fun input => by
      unfold finalCoordinatedSelectedOccurrenceData?
      cases finalCoordinatedScaledClause? input.1.1 input.1.2 <;> rfl

private def finalCoordinatedSelectedOccurrenceInput
    {Variable : Type*}
    (input : RetainedFinalFallbackQuery Variable ×
      FinalCoordinatedSelectedOccurrenceData Variable) :
    FinalCoordinatedSuffixQuery Variable :=
  ((((input.1.1.1, input.2.1), input.2.2), input.1.1.2), input.1.2)

private theorem finalCoordinatedSelectedOccurrenceInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedSelectedOccurrenceInput
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

private def finalCoordinatedSelectedOrdinaryRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable ×
      FinalCoordinatedSelectedOccurrenceData Variable) : List Cell :=
  finalCoordinatedOrdinaryRouteComputed
    (finalCoordinatedSelectedOccurrenceInput input)

private theorem finalCoordinatedSelectedOrdinaryRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedOrdinaryRoute
      (Variable := Variable)) :=
  finalCoordinatedOrdinaryRouteComputed_primrec.comp
    finalCoordinatedSelectedOccurrenceInput_primrec

private def finalCoordinatedOrdinaryOccurrenceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  match finalCoordinatedSelectedOccurrenceData? input with
  | none => []
  | some data => finalCoordinatedSelectedOrdinaryRoute (input, data)

private theorem finalCoordinatedOrdinaryOccurrenceLookup_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedOrdinaryOccurrenceLookup
      (Variable := Variable)) := by
  exact (Primrec.option_casesOn
    finalCoordinatedSelectedOccurrenceData?_primrec
    (Primrec.const [])
    finalCoordinatedSelectedOrdinaryRoute_primrec.to₂).of_eq
      fun input => by
        unfold finalCoordinatedOrdinaryOccurrenceLookup
        cases finalCoordinatedSelectedOccurrenceData? input <;> rfl

private theorem finalCoordinatedSelectedOrdinaryRoute_eq_spliced
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable)
    (clause : PositionedPeriodicClause
      (FinalCoordinatedVariable Variable))
    (literal : PeriodicLiteral (FinalCoordinatedVariable Variable))
    (clauseLookup :
      (finalCoordinatedScaledSource input.1.1).clauses[input.1.2]? =
        some clause)
    (literalLookup : clause.literals[input.2]? = some literal) :
    finalCoordinatedSelectedOrdinaryRoute
        (input, (angularClauseRouteData clause,
          PeriodicLiteral.equivData literal)) =
      retainedAngularFanSplicedOccurrenceRoute
        (finalCoordinatedScaledSource input.1.1)
        (finalCoordinatedScaledPlacement input.1.1)
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes input.1.1))
        clause literal input.1.2 input.2 := by
  unfold finalCoordinatedSelectedOrdinaryRoute
    finalCoordinatedSelectedOccurrenceInput
    finalCoordinatedOrdinaryRouteComputed
    finalCoordinatedOrdinaryPrefix
    finalCoordinatedOrdinaryBoundaryInput
    finalCoordinatedOrdinaryScaledTerminal
    finalCoordinatedEscapedScaledRoute
    finalCoordinatedEscapedRawRoute
    finalCoordinatedEscapedSuffix
    retainedAngularFanSplicedBoundaryRouteQuery
    retainedAngularFanSplicedOccurrenceRoute
    retainedAngularFanBoundaryIncidenceRoutes
    PositionedPeriodicCNF.scaleIncidenceRoutes
  simp only [angularLiteralOfRouteData_equivData,
    clauseLookup, literalLookup]
  have suffixEq := finalCoordinatedOccurrenceSuffix_eq_flat
    (finalCoordinatedSelectedOccurrenceInput
      (input, (angularClauseRouteData clause,
        PeriodicLiteral.equivData literal)))
  simp only [finalCoordinatedSelectedOccurrenceInput,
    angularClauseOfRouteData_routeData,
    angularLiteralOfRouteData_equivData] at suffixEq
  have slotEq :
      retainedFinalCoordinatedOccurrenceSlot
          input.1.1 literal input.1.2 input.2 =
        boundedRetainedTerminalSlot
          (angularOccurrenceIndex
            (angularOccurrenceOrder
              (finalCoordinatedScaledSource input.1.1).erase
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes input.1.1)))
            literal input.1.2 input.2) := by
    rfl
  have suffixEq' :
      angularOccurrenceSuffix
          (finalCoordinatedScaledPlacement input.1.1)
          (angularOccurrenceOrder
            (finalCoordinatedScaledSource input.1.1).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes input.1.1)))
          clause literal input.1.2 input.2 =
        finalCoordinatedFlatOccurrenceSuffix
          ((((input.1.1, angularClauseRouteData clause),
            PeriodicLiteral.equivData literal), input.1.2), input.2) := by
    simpa [finalCoordinatedScaledOrder] using suffixEq
  have slotEq' :
      retainedFinalCoordinatedOccurrenceSlot
          input.1.1 literal input.1.2 input.2 =
        boundedRetainedTerminalSlot
          (angularOccurrenceIndex
            (angularOccurrenceOrder
              (finalCoordinatedScaledSource input.1.1).erase
              (fun clauseIndex literalIndex =>
                scalePolyline retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes input.1.1
                    clauseIndex literalIndex)))
            literal input.1.2 input.2) :=
    slotEq
  have suffixEq'' :
      angularOccurrenceSuffix
          (finalCoordinatedScaledPlacement input.1.1)
          (angularOccurrenceOrder
            (finalCoordinatedScaledSource input.1.1).erase
            (fun clauseIndex literalIndex =>
              scalePolyline retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes input.1.1
                  clauseIndex literalIndex)))
          clause literal input.1.2 input.2 =
        finalCoordinatedFlatOccurrenceSuffix
          ((((input.1.1, angularClauseRouteData clause),
            PeriodicLiteral.equivData literal), input.1.2), input.2) :=
    suffixEq'
  rw [slotEq', suffixEq'']

private theorem finalCoordinatedOrdinaryOccurrenceLookup_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    finalCoordinatedOrdinaryOccurrenceLookup input =
      retainedAngularFanSplicedOccurrenceRoutes
        (finalCoordinatedScaledSource input.1.1)
        (finalCoordinatedScaledPlacement input.1.1)
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes input.1.1))
        input.1.2 input.2 := by
  have clauseQueryEq :
      finalCoordinatedScaledClause? input.1.1 input.1.2 =
        (finalCoordinatedScaledSource input.1.1).clauses[input.1.2]? := by
    rfl
  cases clauseLookup :
      (finalCoordinatedScaledSource input.1.1).clauses[input.1.2]? with
  | none =>
      have queryLookup :
          finalCoordinatedScaledClause? input.1.1 input.1.2 = none :=
        clauseQueryEq.trans clauseLookup
      have selectedNone :
          finalCoordinatedSelectedOccurrenceData? input = none := by
        simp [finalCoordinatedSelectedOccurrenceData?, queryLookup]
      rw [show finalCoordinatedOrdinaryOccurrenceLookup input = [] by
        simp [finalCoordinatedOrdinaryOccurrenceLookup, selectedNone]]
      simp [retainedAngularFanSplicedOccurrenceRoutes, clauseLookup]
  | some clause =>
      have queryLookup :
          finalCoordinatedScaledClause? input.1.1 input.1.2 = some clause :=
        clauseQueryEq.trans clauseLookup
      cases literalLookup : clause.literals[input.2]? with
      | none =>
          have selectedNone :
              finalCoordinatedSelectedOccurrenceData? input = none := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, queryLookup,
              literalLookup]
          rw [show finalCoordinatedOrdinaryOccurrenceLookup input = [] by
            simp [finalCoordinatedOrdinaryOccurrenceLookup, selectedNone]]
          simp [retainedAngularFanSplicedOccurrenceRoutes,
            clauseLookup, literalLookup]
      | some literal =>
          have selectedSome :
              finalCoordinatedSelectedOccurrenceData? input =
                some (angularClauseRouteData clause,
                  PeriodicLiteral.equivData literal) := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, queryLookup,
              literalLookup]
          rw [show finalCoordinatedOrdinaryOccurrenceLookup input =
              finalCoordinatedSelectedOrdinaryRoute
                (input, (angularClauseRouteData clause,
                  PeriodicLiteral.equivData literal)) by
            simp [finalCoordinatedOrdinaryOccurrenceLookup, selectedSome]]
          rw [show retainedAngularFanSplicedOccurrenceRoutes
              (finalCoordinatedScaledSource input.1.1)
              (finalCoordinatedScaledPlacement input.1.1)
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes input.1.1))
              input.1.2 input.2 =
                retainedAngularFanSplicedOccurrenceRoute
                  (finalCoordinatedScaledSource input.1.1)
                  (finalCoordinatedScaledPlacement input.1.1)
                  (PositionedPeriodicCNF.scaleIncidenceRoutes
                    retainedAngularFanSourceClearanceFactor
                    (finalCoordinatedSourceRoutes input.1.1))
                  clause literal input.1.2 input.2 by
            simp [retainedAngularFanSplicedOccurrenceRoutes,
              clauseLookup, literalLookup]]
          exact finalCoordinatedSelectedOrdinaryRoute_eq_spliced
            input clause literal clauseLookup literalLookup

private def finalCoordinatedScaledSourceClauseLength
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Nat :=
  (finalCoordinatedScaledSource formula).clauses.length

private theorem finalCoordinatedScaledSourceClauseLength_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedScaledSourceClauseLength
      (Variable := Variable)) :=
  Primrec.list_length.comp
    (PositionedPeriodicCNF.clauses_primrec.comp
      finalCoordinatedScaledSource_primrec)

private def finalCoordinatedCycleMetadataList
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :=
  allCycleClauseMetadata
    (finalCoordinatedScaledSource formula)
    (finalCoordinatedScaledPlacement formula)

private theorem finalCoordinatedCycleMetadataList_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedCycleMetadataList
      (Variable := Variable)) := by
  exact (PeriodicEightOccurrenceSplitPositioned.allCycleClauseMetadata_primrec
    (Input := PeriodicCNF Variable)
    (Variable := FinalCoordinatedVariable Variable)
    finalCoordinatedScaledSource finalCoordinatedScaledPlacement
    finalCoordinatedScaledSource_primrec
    finalCoordinatedScaledPlacement_position_primrec).of_eq fun _ => rfl

private abbrev FinalCoordinatedCycleOriginQuery (Variable : Type*) :=
  PeriodicCNF Variable × FinalCoordinatedVariable Variable

private def finalCoordinatedCycleOrigin
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedCycleOriginQuery Variable) : Cell :=
  Cell.sub
    (Cell.scale refinementScale
      ((finalCoordinatedScaledPlacement input.1).position input.2))
    (12, 12)

private theorem finalCoordinatedCycleOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedCycleOrigin
      (Variable := Variable)) := by
  have scaled : Primrec fun input :
      FinalCoordinatedCycleOriginQuery Variable =>
      Cell.scale refinementScale
        ((finalCoordinatedScaledPlacement input.1).position input.2) :=
    Computability.cell_scale_primrec.comp
      (Primrec.const refinementScale)
      finalCoordinatedScaledPlacement_position_primrec
  exact (Computability.cell_sub_primrec.comp scaled
    (Primrec.const ((12, 12) : Cell))).of_eq fun _ => rfl

private abbrev FinalCoordinatedSelectedCycleQuery (Variable : Type*) :=
  RetainedFinalFallbackQuery Variable ×
    CycleClauseMetadata (FinalCoordinatedVariable Variable)

private def finalCoordinatedSelectedCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSelectedCycleQuery Variable) : List Cell :=
  (OccurrenceSplitRing.cycleRoutes
    input.2.localClauseIndex input.1.2).map fun point =>
      Cell.add
        (finalCoordinatedCycleOrigin (input.1.1.1, input.2.atom))
        point

private theorem finalCoordinatedSelectedCycleRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedCycleRoute
      (Variable := Variable)) := by
  let Query := FinalCoordinatedSelectedCycleQuery Variable
  have route : Primrec fun input : Query =>
      OccurrenceSplitRing.cycleRoutes
        input.2.localClauseIndex input.1.2 :=
    OccurrenceSplitRing.cycleRoutes_primrec.comp
      (Primrec.pair
        (CycleClauseMetadata.localClauseIndex_primrec.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have origin : Primrec fun input : Query =>
      finalCoordinatedCycleOrigin (input.1.1.1, input.2.atom) :=
    finalCoordinatedCycleOrigin_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))
        (CycleClauseMetadata.atom_primrec.comp Primrec.snd))
  exact (Primrec.list_map route
    (Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

private theorem finalCoordinatedSelectedCycleRoute_eq_positioned
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSelectedCycleQuery Variable) :
    finalCoordinatedSelectedCycleRoute input =
      positionedCycleRoutes
        (finalCoordinatedScaledPlacement input.1.1.1)
        input.2.atom input.2.localClauseIndex input.1.2 := by
  rfl

private def finalCoordinatedSelectedCycleMetadata?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :=
  (finalCoordinatedCycleMetadataList input.1.1)[
    input.1.2 - finalCoordinatedScaledSourceClauseLength input.1.1]?

private theorem finalCoordinatedSelectedCycleMetadata?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedCycleMetadata?
      (Variable := Variable)) := by
  have items : Primrec fun input : RetainedFinalFallbackQuery Variable =>
      finalCoordinatedCycleMetadataList input.1.1 :=
    finalCoordinatedCycleMetadataList_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have index : Primrec fun input : RetainedFinalFallbackQuery Variable =>
      input.1.2 - finalCoordinatedScaledSourceClauseLength input.1.1 :=
    Primrec.nat_sub.comp
      (Primrec.snd.comp Primrec.fst)
      (finalCoordinatedScaledSourceClauseLength_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  exact (Primrec.list_getElem?.comp items index).of_eq fun _ => rfl

private def finalCoordinatedRawCycleRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  match finalCoordinatedSelectedCycleMetadata? input with
  | none => []
  | some metadata => finalCoordinatedSelectedCycleRoute (input, metadata)

private theorem finalCoordinatedRawCycleRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedRawCycleRouteComputed
      (Variable := Variable)) := by
  exact (Primrec.option_casesOn
    finalCoordinatedSelectedCycleMetadata?_primrec
    (Primrec.const [])
    finalCoordinatedSelectedCycleRoute_primrec.to₂).of_eq fun input => by
      unfold finalCoordinatedRawCycleRouteComputed
      cases finalCoordinatedSelectedCycleMetadata? input <;> rfl

private def finalCoordinatedCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    (allCycleRoutes
      (finalCoordinatedScaledSource input.1.1)
      (finalCoordinatedScaledPlacement input.1.1)
      (input.1.2 - finalCoordinatedScaledSourceClauseLength input.1.1)
      input.2)

private def finalCoordinatedCycleRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    (finalCoordinatedRawCycleRouteComputed input)

private theorem finalCoordinatedCycleRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedCycleRouteComputed
      (Variable := Variable)) := by
  exact (scalePolyline_primrec.comp
    (Primrec.const (retainedTerminalFanRoutingRefinement : Int))
    finalCoordinatedRawCycleRouteComputed_primrec).of_eq fun _ => rfl

private theorem finalCoordinatedCycleRouteComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    finalCoordinatedCycleRouteComputed input =
      finalCoordinatedCycleRoute input := by
  unfold finalCoordinatedCycleRouteComputed finalCoordinatedCycleRoute
    finalCoordinatedRawCycleRouteComputed
    finalCoordinatedSelectedCycleMetadata?
    finalCoordinatedCycleMetadataList allCycleRoutes
  cases h : (allCycleClauseMetadata
    (finalCoordinatedScaledSource input.1.1)
    (finalCoordinatedScaledPlacement input.1.1))[
      input.1.2 -
        finalCoordinatedScaledSourceClauseLength input.1.1]? with
  | none => rfl
  | some metadata =>
      change scalePolyline retainedTerminalFanRoutingRefinement
          (finalCoordinatedSelectedCycleRoute (input, metadata)) =
        scalePolyline retainedTerminalFanRoutingRefinement
          (positionedCycleRoutes
            (finalCoordinatedScaledPlacement input.1.1)
            metadata.atom metadata.localClauseIndex input.2)
      rw [finalCoordinatedSelectedCycleRoute_eq_positioned]

private theorem finalCoordinatedCycleRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedCycleRoute
      (Variable := Variable)) :=
  finalCoordinatedCycleRouteComputed_primrec.of_eq fun input =>
    finalCoordinatedCycleRouteComputed_eq input

private def finalCoordinatedEstablishedRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  if input.1.2 <
      finalCoordinatedScaledSourceClauseLength input.1.1 then
    finalCoordinatedOrdinaryOccurrenceLookup input
  else
    finalCoordinatedCycleRoute input

private theorem finalCoordinatedEstablishedRouteComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    finalCoordinatedEstablishedRouteComputed input =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  unfold retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
    retainedAngularFanSourceScaledSplicedIncidenceRoutes
  change finalCoordinatedEstablishedRouteComputed input =
    retainedAngularFanSplicedIncidenceRoutes
      (finalCoordinatedScaledSource input.1.1)
      (finalCoordinatedScaledPlacement input.1.1)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes input.1.1))
      input.1.2 input.2
  have occurrenceCount :
      (occurrenceClauses
        (finalCoordinatedScaledSource input.1.1)
        (occurrencePortsOfAngularOrder
          (finalCoordinatedScaledSource input.1.1).erase
          (angularOccurrenceOrder
            (finalCoordinatedScaledSource input.1.1).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes input.1.1))))).length =
        finalCoordinatedScaledSourceClauseLength input.1.1 := by
    simp [PeriodicEightOccurrenceSplitPositioned.occurrenceClauses,
      finalCoordinatedScaledSourceClauseLength]
  by_cases occurrenceIndex : input.1.2 <
      finalCoordinatedScaledSourceClauseLength input.1.1
  · have occurrenceIndex' :
        input.1.2 <
          (occurrenceClauses
            (finalCoordinatedScaledSource input.1.1)
            (occurrencePortsOfAngularOrder
              (finalCoordinatedScaledSource input.1.1).erase
              (angularOccurrenceOrder
                (finalCoordinatedScaledSource input.1.1).erase
                (PositionedPeriodicCNF.scaleIncidenceRoutes
                  retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes input.1.1))))).length := by
      rwa [occurrenceCount]
    rw [retainedAngularFanSplicedIncidenceRoutes_occurrence
      _ _ _ input.1.2 input.2 occurrenceIndex']
    unfold finalCoordinatedEstablishedRouteComputed
    rw [if_pos occurrenceIndex]
    exact finalCoordinatedOrdinaryOccurrenceLookup_eq input
  · have occurrenceIndex' :
        ¬ input.1.2 <
          (occurrenceClauses
            (finalCoordinatedScaledSource input.1.1)
            (occurrencePortsOfAngularOrder
              (finalCoordinatedScaledSource input.1.1).erase
              (angularOccurrenceOrder
                (finalCoordinatedScaledSource input.1.1).erase
                (PositionedPeriodicCNF.scaleIncidenceRoutes
                  retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes input.1.1))))).length := by
      rwa [occurrenceCount]
    unfold finalCoordinatedEstablishedRouteComputed
      retainedAngularFanSplicedIncidenceRoutes
    rw [if_neg occurrenceIndex, if_neg occurrenceIndex', occurrenceCount]
    rfl

private theorem finalCoordinatedEstablishedRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEstablishedRouteComputed
      (Variable := Variable)) := by
  let Query := RetainedFinalFallbackQuery Variable
  have beforeCycles : PrimrecPred fun input : Query =>
      input.1.2 <
        finalCoordinatedScaledSourceClauseLength input.1.1 :=
    Primrec.nat_lt.comp
      (Primrec.snd.comp Primrec.fst)
      (finalCoordinatedScaledSourceClauseLength_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  exact Primrec.ite beforeCycles
    finalCoordinatedOrdinaryOccurrenceLookup_primrec
    finalCoordinatedCycleRoute_primrec

abbrev RetainedFinalEstablishedRouteQuery (Variable : Type*) :=
  RetainedFinalFallbackQuery Variable

/-- Uncurried exact lookup for the established source-scaled retained route
family used by every non-substituted final branch. -/
def retainedFinalEstablishedRouteQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalEstablishedRouteQuery Variable) : List Cell :=
  retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
    input.1.1 input.1.2 input.2

private theorem retainedFinalEstablishedRouteQuery_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalEstablishedRouteQuery Variable) :
    retainedFinalEstablishedRouteQuery input =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  rfl

/-- The established ordinary-occurrence and implication-cycle route lookup
is primitive recursive. -/
theorem retainedFinalEstablishedRouteQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalEstablishedRouteQuery
      (Variable := Variable)) := by
  exact finalCoordinatedEstablishedRouteComputed_primrec.of_eq fun input =>
    finalCoordinatedEstablishedRouteComputed_eq input

/-! ## Total coordinated route dispatcher -/

private def finalCoordinatedSelectedEscapedRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable ×
      FinalCoordinatedSelectedOccurrenceData Variable) : List Cell :=
  retainedFinalEscapedFallbackOccurrenceRouteQuery
    (finalCoordinatedSelectedOccurrenceInput input)

private theorem finalCoordinatedSelectedEscapedRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedEscapedRoute
      (Variable := Variable)) :=
  retainedFinalEscapedFallbackOccurrenceRoute_primrec.comp
    finalCoordinatedSelectedOccurrenceInput_primrec

private theorem finalCoordinatedSelectedEscapedRoute_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable)
    (clause : PositionedPeriodicClause
      (FinalCoordinatedVariable Variable))
    (literal : PeriodicLiteral (FinalCoordinatedVariable Variable)) :
    finalCoordinatedSelectedEscapedRoute
        (input, (angularClauseRouteData clause,
          PeriodicLiteral.equivData literal)) =
      retainedFinalEscapedFallbackOccurrenceRoute
        input.1.1 clause literal input.1.2 input.2 := by
  unfold finalCoordinatedSelectedEscapedRoute
    finalCoordinatedSelectedOccurrenceInput
    retainedFinalEscapedFallbackOccurrenceRouteQuery
  simp

private abbrev FinalCoordinatedSelectedChoiceQuery (Variable : Type*) :=
  (RetainedFinalFallbackQuery Variable × RetainedDirectSourceRouteChoice) ×
    FinalCoordinatedSelectedOccurrenceData Variable

private def finalCoordinatedSelectedDirectInput
    {Variable : Type*}
    (input : FinalCoordinatedSelectedChoiceQuery Variable) :
    RetainedFinalCoordinatedDirectRouteQuery Variable :=
  (((((input.1.1.1.1, input.1.2), input.2.1), input.2.2),
    input.1.1.1.2), input.1.1.2)

private theorem finalCoordinatedSelectedDirectInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (finalCoordinatedSelectedDirectInput
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))

private def finalCoordinatedSelectedDirectRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedSelectedChoiceQuery Variable) : List Cell :=
  retainedFinalCoordinatedDirectOccurrenceRouteQuery
    (finalCoordinatedSelectedDirectInput input)

private theorem finalCoordinatedSelectedDirectRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedSelectedDirectRoute
      (Variable := Variable)) :=
  retainedFinalCoordinatedDirectOccurrenceRoute_primrec.comp
    finalCoordinatedSelectedDirectInput_primrec

private theorem finalCoordinatedSelectedDirectRoute_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable)
    (choice : RetainedDirectSourceRouteChoice)
    (clause : PositionedPeriodicClause
      (FinalCoordinatedVariable Variable))
    (literal : PeriodicLiteral (FinalCoordinatedVariable Variable)) :
    finalCoordinatedSelectedDirectRoute
        ((input, choice), (angularClauseRouteData clause,
          PeriodicLiteral.equivData literal)) =
      retainedFinalCoordinatedDirectOccurrenceRoute
        input.1.1 choice clause literal input.1.2 input.2 := by
  unfold finalCoordinatedSelectedDirectRoute
    finalCoordinatedSelectedDirectInput
    retainedFinalCoordinatedDirectOccurrenceRouteQuery
  simp

private def finalCoordinatedEscapedOccurrenceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  match finalCoordinatedSelectedOccurrenceData? input with
  | none => retainedFinalEstablishedRouteQuery input
  | some data => finalCoordinatedSelectedEscapedRoute (input, data)

private theorem finalCoordinatedEscapedOccurrenceLookup_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedEscapedOccurrenceLookup
      (Variable := Variable)) := by
  exact (Primrec.option_casesOn
    finalCoordinatedSelectedOccurrenceData?_primrec
    retainedFinalEstablishedRouteQuery_primrec
    finalCoordinatedSelectedEscapedRoute_primrec.to₂).of_eq fun input => by
      unfold finalCoordinatedEscapedOccurrenceLookup
      cases finalCoordinatedSelectedOccurrenceData? input <;> rfl

private def finalCoordinatedNoChoiceRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  bif retainedFinalFallbackUsesEscapeQuery input then
    finalCoordinatedEscapedOccurrenceLookup input
  else
    retainedFinalEstablishedRouteQuery input

private theorem finalCoordinatedNoChoiceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedNoChoiceRoute
      (Variable := Variable)) := by
  exact Primrec.cond retainedFinalFallbackUsesEscapeQuery_primrec
    finalCoordinatedEscapedOccurrenceLookup_primrec
    retainedFinalEstablishedRouteQuery_primrec

private abbrev FinalCoordinatedChoiceQuery (Variable : Type*) :=
  RetainedFinalFallbackQuery Variable × RetainedDirectSourceRouteChoice

private def finalCoordinatedChoiceRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedChoiceQuery Variable) : List Cell :=
  match finalCoordinatedSelectedOccurrenceData? input.1 with
  | none => retainedFinalEstablishedRouteQuery input.1
  | some data => finalCoordinatedSelectedDirectRoute (input, data)

private theorem finalCoordinatedChoiceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (finalCoordinatedChoiceRoute
      (Variable := Variable)) := by
  have selected : Primrec fun input : FinalCoordinatedChoiceQuery Variable =>
      finalCoordinatedSelectedOccurrenceData? input.1 :=
    finalCoordinatedSelectedOccurrenceData?_primrec.comp Primrec.fst
  have established : Primrec fun input :
      FinalCoordinatedChoiceQuery Variable =>
      retainedFinalEstablishedRouteQuery input.1 :=
    retainedFinalEstablishedRouteQuery_primrec.comp Primrec.fst
  exact (Primrec.option_casesOn selected established
    finalCoordinatedSelectedDirectRoute_primrec.to₂).of_eq fun input => by
      unfold finalCoordinatedChoiceRoute
      cases finalCoordinatedSelectedOccurrenceData? input.1 <;> rfl

/-- Proof-free staged implementation of the final direct/escaped/ordinary
route dispatcher. -/
def retainedFinalCoordinatedRouteComputed
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  match retainedFinalDirectSourceRouteChoice?
      input.1.1 input.1.2 input.2 with
  | none => finalCoordinatedNoChoiceRoute input
  | some choice => finalCoordinatedChoiceRoute (input, choice)

/-- The staged total route dispatcher is primitive recursive. -/
theorem retainedFinalCoordinatedRouteComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalCoordinatedRouteComputed
      (Variable := Variable)) := by
  exact (Primrec.option_casesOn
    retainedFinalDirectSourceRouteChoice?_primrec
    finalCoordinatedNoChoiceRoute_primrec
    finalCoordinatedChoiceRoute_primrec.to₂).of_eq fun input => by
      unfold retainedFinalCoordinatedRouteComputed
      cases retainedFinalDirectSourceRouteChoice?
        input.1.1 input.1.2 input.2 <;> rfl

private def finalCoordinatedEscapedRouteFromSourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) : List Cell :=
  match finalCoordinatedScaledClause? input.1.1 input.1.2 with
  | none =>
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2
  | some clause =>
      match clause.literals[input.2]? with
      | none =>
          retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
            input.1.1 input.1.2 input.2
      | some literal =>
          retainedFinalEscapedFallbackOccurrenceRoute
            input.1.1 clause literal input.1.2 input.2

private theorem finalCoordinatedEscapedOccurrenceLookup_eq_sourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    finalCoordinatedEscapedOccurrenceLookup input =
      finalCoordinatedEscapedRouteFromSourceLookup input := by
  unfold finalCoordinatedEscapedOccurrenceLookup
    finalCoordinatedEscapedRouteFromSourceLookup
  cases clauseLookup :
      finalCoordinatedScaledClause? input.1.1 input.1.2 with
  | none =>
      have selectedNone :
          finalCoordinatedSelectedOccurrenceData? input = none := by
        simp [finalCoordinatedSelectedOccurrenceData?, clauseLookup]
      rw [selectedNone]
      simpa only using retainedFinalEstablishedRouteQuery_eq input
  | some clause =>
      cases literalLookup : clause.literals[input.2]? with
      | none =>
          have selectedNone :
              finalCoordinatedSelectedOccurrenceData? input = none := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, clauseLookup,
              literalLookup]
          rw [selectedNone]
          simp [literalLookup]
          exact retainedFinalEstablishedRouteQuery_eq input
      | some literal =>
          have selectedSome :
              finalCoordinatedSelectedOccurrenceData? input =
                some (angularClauseRouteData clause,
                  PeriodicLiteral.equivData literal) := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, clauseLookup,
              literalLookup]
          rw [selectedSome]
          simp only [literalLookup]
          exact finalCoordinatedSelectedEscapedRoute_eq
            input clause literal

private def finalCoordinatedDirectRouteFromSourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedChoiceQuery Variable) : List Cell :=
  match finalCoordinatedScaledClause? input.1.1.1 input.1.1.2 with
  | none =>
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        input.1.1.1 input.1.1.2 input.1.2
  | some clause =>
      match clause.literals[input.1.2]? with
      | none =>
          retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
            input.1.1.1 input.1.1.2 input.1.2
      | some literal =>
          retainedFinalCoordinatedDirectOccurrenceRoute
            input.1.1.1 input.2 clause literal input.1.1.2 input.1.2

private theorem finalCoordinatedChoiceRoute_eq_sourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : FinalCoordinatedChoiceQuery Variable) :
    finalCoordinatedChoiceRoute input =
      finalCoordinatedDirectRouteFromSourceLookup input := by
  unfold finalCoordinatedChoiceRoute
    finalCoordinatedDirectRouteFromSourceLookup
  cases clauseLookup :
      finalCoordinatedScaledClause? input.1.1.1 input.1.1.2 with
  | none =>
      have selectedNone :
          finalCoordinatedSelectedOccurrenceData? input.1 = none := by
        simp [finalCoordinatedSelectedOccurrenceData?, clauseLookup]
      rw [selectedNone]
      rfl
  | some clause =>
      cases literalLookup : clause.literals[input.1.2]? with
      | none =>
          have selectedNone :
              finalCoordinatedSelectedOccurrenceData? input.1 = none := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, clauseLookup,
              literalLookup]
          rw [selectedNone]
          simp [literalLookup]
          rfl
      | some literal =>
          have selectedSome :
              finalCoordinatedSelectedOccurrenceData? input.1 =
                some (angularClauseRouteData clause,
                  PeriodicLiteral.equivData literal) := by
            simp [finalCoordinatedSelectedOccurrenceData?,
              finalCoordinatedSelectedLiteralData?, clauseLookup,
              literalLookup]
          rw [selectedSome]
          simp only [literalLookup]
          exact finalCoordinatedSelectedDirectRoute_eq
            input.1 input.2 clause literal

private theorem finalCoordinatedNoChoiceRoute_eq_sourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    finalCoordinatedNoChoiceRoute input =
      bif retainedFinalFallbackUsesEscapeQuery input then
        finalCoordinatedEscapedRouteFromSourceLookup input
      else
        retainedFinalEstablishedRouteQuery input := by
  unfold finalCoordinatedNoChoiceRoute
  rw [finalCoordinatedEscapedOccurrenceLookup_eq_sourceLookup]

private theorem finalCoordinatedPublicRoute_eq_sourceLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2 =
      match retainedFinalDirectSourceRouteChoice?
          input.1.1 input.1.2 input.2 with
      | none =>
          bif retainedFinalFallbackUsesEscapeQuery input then
            finalCoordinatedEscapedRouteFromSourceLookup input
          else
            retainedFinalEstablishedRouteQuery input
      | some choice =>
          finalCoordinatedDirectRouteFromSourceLookup (input, choice) := by
  cases choiceLookup : retainedFinalDirectSourceRouteChoice?
      input.1.1 input.1.2 input.2 with
  | none =>
      unfold
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      rw [choiceLookup]
      simp only
      cases escapeLookup : retainedFinalFallbackUsesEscape
          input.1.1 input.1.2 input.2 with
      | false =>
          unfold retainedFinalFallbackUsesEscapeQuery
          rw [escapeLookup]
          simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
          rfl
      | true =>
          unfold retainedFinalFallbackUsesEscapeQuery
          rw [escapeLookup]
          simp only [↓reduceIte, cond_true]
          unfold finalCoordinatedEscapedRouteFromSourceLookup
          cases finalCoordinatedScaledClause?
              input.1.1 input.1.2 with
          | none => rfl
          | some clause =>
              cases clause.literals[input.2]? <;> rfl
  | some choice =>
      unfold
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      rw [choiceLookup]
      simp only
      unfold finalCoordinatedDirectRouteFromSourceLookup
      cases finalCoordinatedScaledClause?
          input.1.1 input.1.2 with
      | none => rfl
      | some clause =>
          cases clause.literals[input.2]? <;> rfl

/-- The staged dispatcher is extensionally the exact final coordinated route
family, including all malformed-index fallbacks. -/
theorem retainedFinalCoordinatedRouteComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalFallbackQuery Variable) :
    retainedFinalCoordinatedRouteComputed input =
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  rw [finalCoordinatedPublicRoute_eq_sourceLookup]
  unfold retainedFinalCoordinatedRouteComputed
  cases choiceLookup : retainedFinalDirectSourceRouteChoice?
      input.1.1 input.1.2 input.2 with
  | none =>
      exact finalCoordinatedNoChoiceRoute_eq_sourceLookup input
  | some choice =>
      exact finalCoordinatedChoiceRoute_eq_sourceLookup (input, choice)

abbrev RetainedFinalCoordinatedRouteQuery (Variable : Type*) :=
  RetainedFinalFallbackQuery Variable

/-- Uncurried lookup of the exact final coordinated fixed-eight incidence
route family. -/
def retainedFinalCoordinatedRouteQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalCoordinatedRouteQuery Variable) : List Cell :=
  retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
    input.1.1 input.1.2 input.2

/-- The exact final direct/escaped/ordinary/cycle route dispatcher is
primitive recursive. -/
theorem retainedFinalCoordinatedRouteQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalCoordinatedRouteQuery
      (Variable := Variable)) :=
  retainedFinalCoordinatedRouteComputed_primrec.of_eq fun input =>
    retainedFinalCoordinatedRouteComputed_eq input

/-! ## Normalized routes and first directions -/

abbrev RetainedFinalNormalizedRouteQuery (Variable : Type*) :=
  RetainedFinalFallbackQuery Variable

/-- Uncurried lookup of the final unit-subdivided, loop-erased route family. -/
def retainedFinalNormalizedRouteQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalNormalizedRouteQuery Variable) : List Cell :=
  retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
    input.1.1 input.1.2 input.2

/-- The exact final normalized route lookup is primitive recursive. -/
theorem retainedFinalNormalizedRouteQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalNormalizedRouteQuery
      (Variable := Variable)) := by
  exact (AxisDirection.normalizeOrthogonalPolyline_primrec.comp
    retainedFinalCoordinatedRouteQuery_primrec).of_eq fun input => by
      rfl

abbrev RetainedFinalNormalizedFirstDirectionQuery (Variable : Type*) :=
  RetainedFinalNormalizedRouteQuery Variable

/-- First direction of one final normalized route, with `.invalid` on a
route containing fewer than two points. -/
def retainedFinalNormalizedFirstDirectionQuery
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalNormalizedFirstDirectionQuery Variable) :
    AxisDirection :=
  AxisDirection.polylineFirstDirection
    (retainedFinalNormalizedRouteQuery input)

/-- Final normalized-route first directions are primitive recursive. -/
theorem retainedFinalNormalizedFirstDirectionQuery_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalNormalizedFirstDirectionQuery
      (Variable := Variable)) :=
  PeriodicThreeDM.NormalizationCompiler.polylineFirstDirection_primrec.comp
    retainedFinalNormalizedRouteQuery_primrec

end PeriodicOrthocrossing
end LeanTrominoes

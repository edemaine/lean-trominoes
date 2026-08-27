/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionsTail
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedTailSemantics
import LeanTrominoes.RetainedAngularFanFinalDirectFirstDirections

/-! # Complete tails of final normalized direct-source routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget
open PeriodicEightOccurrenceSplit

/-- A successful direct-source choice exposes exactly its finite normalized
tail-query word at the public final route boundary. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_direct_tailDirections
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex).tail =
      retainedDirectSourceNormalizedTailOfQuery
        (retainedDirectSourceNormalizedTailQueryOfIndex
          choice.kind choice.index
          (retainedFinalCoordinatedOccurrenceSlot
            formula literal clauseIndex literalIndex)) := by
  have sourceClauseLookup :
      (finalCoordinatedSource formula).clauses[clauseIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?
      (x := (clause, clauseIndex))
      (l := (finalCoordinatedSource formula).clauses)).mp clauseMember
  have scaledClauseLookup :
      finalCoordinatedScaledClause? formula clauseIndex =
        some
          (clause.scale retainedAngularFanSourceClearanceFactor) := by
    unfold finalCoordinatedScaledClause?
    rw [PositionedPeriodicCNF.scale_clauses,
      List.getElem?_map, sourceClauseLookup]
    rfl
  have sourceLiteralLookup :
      clause.literals[literalIndex]? = some literal :=
    (List.mem_zipIdx_iff_getElem?
      (x := (literal, literalIndex))
      (l := clause.literals)).mp literalMember
  have scaledLiteralLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[literalIndex]? =
          some literal := by
    simpa using sourceLiteralLookup
  unfold
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup scaledClauseLookup scaledLiteralLookup]
  rw [
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember choiceLookup]
  let slot := retainedFinalCoordinatedOccurrenceSlot
    formula literal clauseIndex literalIndex
  let route := choice.completeFigure7Route slot
  let zeroChoice :=
    retainedDirectSourceZeroChoice choice.kind choice.index
  have choiceEq : choice = zeroChoice.translateOrigin choice.origin := by
    rcases choice with ⟨origin, kind, index⟩
    simp [zeroChoice, retainedDirectSourceZeroChoice,
      RetainedDirectSourceRouteChoice.translateOrigin, Cell.add]
  have routeValid : route ≠ [] ∧ OrthogonalPolyline route := by
    change choice.completeFigure7Route slot ≠ [] ∧
      OrthogonalPolyline (choice.completeFigure7Route slot)
    rw [choiceEq,
      RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
    have zeroValid :=
      retainedDirectSourceZeroCompleteFigure7Route_valid
        choice.kind choice.index slot
    constructor
    · simpa [translatePolyline] using zeroValid.1
    · simpa using
        zeroValid.2.translate
          (retainedDirectSourceFanPositioningOffset choice.origin)
  have unitSteps :
      (AxisDirection.normalizeOrthogonalPolyline route).IsChain
        AxisDirection.IsUnitAxisStep :=
    AxisDirection.normalizeOrthogonalPolyline_unitSteps
      routeValid.1 routeValid.2
  rw [unitSubdivisionDirections_tail_eq_tail_of_unitSteps _ unitSteps]
  exact choice.normalizedCompleteFigure7Route_tail slot

end PeriodicOrthocrossing
end LeanTrominoes

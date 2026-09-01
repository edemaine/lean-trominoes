/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionsTail
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFinalBendNormalizedDirections
import LeanTrominoes.RetainedAngularFanFinalBendPublicRouteUnitSteps
import LeanTrominoes.RetainedAngularFanFinalBendTaggedLiteralInputOccurrence

/-! # Literal tail directions of final retained-bend clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Deleting the public route's first point deletes exactly the first
direction from its normalized bend-model word. -/
theorem FinalBendIndexedOccurrence.publicTailDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          occurrence.retained occurrence.clauseIndex
          occurrence.literalIndex).tail =
      (BendNormalizedFallbackRouteTailRecords.routeDirections
        occurrence.geometry occurrence.localClauseIndex
        occurrence.literalIndex occurrence.slot).tail := by
  rw [Gadget.unitSubdivisionDirections_tail_eq_tail_of_unitSteps _
    occurrence.publicRouteUnitSteps]
  exact congrArg List.tail (by
    simpa only [BendNormalizedFallbackRouteTailRecords.routeDirections,
      FinalBendIndexedOccurrence.geometry] using
      occurrence.publicNormalizedDirections_eq)

/-- Packaged tagged-literal evidence determines the exact public normalized
route-tail word at that literal. -/
theorem FinalBendTaggedLiteralInput.publicTailDirections
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Fin 2}
    (input : FinalBendTaggedLiteralInput source taggedBend clauseIndex
      literal literalIndex) :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          (PeriodicThreeSATThree.formula source) clauseIndex
          literalIndex).tail =
      (BendNormalizedFallbackRouteTailRecords.routeDirections
        { firstPort := taggedBend.1.incomingPort
          secondPort := taggedBend.1.outgoingPort }
        (if taggedBend.2 then 0 else 1) literalIndex
        (retainedFinalCoordinatedOccurrenceSlot
          (PeriodicThreeSATThree.formula source) literal clauseIndex
          literalIndex)).tail := by
  rcases input.occurrence with
    ⟨occurrence, rfl, rfl, rfl, rfl, rfl⟩
  have tailEq := occurrence.publicTailDirections
  cases h : occurrence.taggedBend.2 <;>
    simpa [FinalBendIndexedOccurrence.retained,
      FinalBendIndexedOccurrence.geometry,
      FinalBendIndexedOccurrence.localClauseIndex,
      FinalBendIndexedOccurrence.slot, h] using tailEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes

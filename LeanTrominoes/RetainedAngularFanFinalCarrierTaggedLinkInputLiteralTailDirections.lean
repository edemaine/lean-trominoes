/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionsTail
import LeanTrominoes.RetainedAngularFanFinalCarrierPublicRouteUnitSteps
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkInputLiteralDirections

/-! # Literal tail directions from final retained-carrier link input -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Deleting the public route's first point therefore deletes exactly the
first direction from its finite carrier-model word. -/
theorem FinalCarrierIndexedOccurrence.publicTailDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          occurrence.retained occurrence.clauseIndex
          occurrence.literalIndex).tail =
      (finalCarrierModelDirectionWord occurrence.source
        occurrence.taggedLink nextSlice occurrence.literalIndex
        occurrence.slot).tail := by
  rw [Gadget.unitSubdivisionDirections_tail_eq_tail_of_unitSteps _
    (occurrence.publicRouteUnitSteps nextSlice)]
  exact congrArg List.tail
    (occurrence.publicDirections nextSlice).directions

/-- A matched tagged literal transports the unit-step property using only
the source, clause-index, and literal-index equalities on which its route
depends. -/
theorem FinalCarrierTaggedLiteralOccurrence.publicRouteUnitSteps
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Fin 2}
    (matched : FinalCarrierTaggedLiteralOccurrence source taggedLink
      clauseIndex literal literalIndex)
    (nextSlice : Bool) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      (PeriodicThreeSATThree.formula source) clauseIndex
      literalIndex).IsChain AxisDirection.IsUnitAxisStep := by
  rcases matched with ⟨occurrence, rfl, rfl, rfl, rfl, rfl⟩
  exact occurrence.publicRouteUnitSteps nextSlice

/-- Add one selected literal to packaged tagged-link evidence and recover its
exact public normalized route-tail directions. -/
theorem FinalCarrierTaggedLinkInput.literalPublicTailDirections
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput
      source taggedLink clauseIndex)
    (literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)))
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈
        (normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula source) taggedLink).zipIdx)
    (nextSlice : Bool) :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          (PeriodicThreeSATThree.formula source) clauseIndex
          literalIndex).tail =
      (finalCarrierModelDirectionWord source taggedLink nextSlice literalIndex
        (retainedFinalCoordinatedOccurrenceSlot
          (PeriodicThreeSATThree.formula source)
          literal clauseIndex literalIndex)).tail := by
  let literalInput : FinalCarrierTaggedLiteralInput
      source taggedLink clauseIndex literal literalIndex :=
    { linkInput := input
      literalMember := literalMember }
  have routeUnitSteps :=
    literalInput.occurrence.publicRouteUnitSteps nextSlice
  rw [Gadget.unitSubdivisionDirections_tail_eq_tail_of_unitSteps _
    routeUnitSteps]
  exact congrArg List.tail
    (input.literalPublicDirections literal literalIndex literalMember
      nextSlice).directions

end PeriodicEightOccurrenceSplit
end LeanTrominoes

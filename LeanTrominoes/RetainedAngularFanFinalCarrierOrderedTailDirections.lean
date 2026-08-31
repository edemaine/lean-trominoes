/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineBinaryTailSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierRoutedProfileSemantics

/-! # Clockwise semantic tails of final retained-carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree
open UnaryProgramClauseProfile

local instance finalCarrierOrderedTailsThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Once the two presentation-order tails are known, a tagged final carrier
clause has exactly the clockwise tail order used by the carrier formatter. -/
theorem FinalCarrierTaggedLinkInput.orderedTailDirections_eq_of_tails
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput source taggedLink clauseIndex)
    (firstTail secondTail : List AxisDirection)
    (firstTailEq :
      Gadget.unitSubdivisionDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            (PeriodicThreeSATThree.formula source) clauseIndex 0).tail =
        firstTail)
    (secondTailEq :
      Gadget.unitSubdivisionDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            (PeriodicThreeSATThree.formula source) clauseIndex 1).tail =
        secondTail) :
    orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          (PeriodicThreeSATThree.formula source))
        clauseIndex
        (copiedOccurrenceClause
          (PeriodicThreeSATThree.formula source) clauseIndex
          ⟨(0, 0), normalizedCarrierClauseAt
            (PeriodicThreeSATThree.formula source) taggedLink⟩) =
      if taggedLink.2 then
        [secondTail, firstTail]
      else if taggedLink.1.first.isHorizontal then
        [secondTail, firstTail]
      else
        [firstTail, secondTail] := by
  let retained := PeriodicThreeSATThree.formula source
  let positionedClause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)) :=
    ⟨(0, 0), normalizedCarrierClauseAt retained taggedLink⟩
  let copiedClause := copiedOccurrenceClause retained clauseIndex
    positionedClause
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      retained
  have lengthEq : copiedClause.literals.length = 2 := by
    rcases taggedLink with ⟨link, forward⟩
    cases forward <;>
      simp [copiedClause, positionedClause, copiedOccurrenceClause,
        PeriodicEightOccurrenceSplit.occurrenceClause,
        normalizedCarrierClauseAt, PeriodicEquality.normalizedClause]
  rcases taggedLink with ⟨link, forward⟩
  cases forward with
  | false =>
      have profileEq := input.routedProfile_eq_carrier
      have binaryProfile :
          DirectedClauseProfile.ofClause routes clauseIndex copiedClause =
            .binary ⟨false, false⟩
              (carrierLensRouteFirstDirection
                link.first.isHorizontal 1 0)
              ⟨carrierLinkNextSlice retained link, true⟩
              (carrierLensRouteFirstDirection
                link.first.isHorizontal 1 1) := by
        simpa [retained, positionedClause, copiedClause, routes,
          routedCopiedClauseProfile,
          BinaryRouteTailRecordFormatter.descriptorProfile,
          carrierClauseDescriptor] using profileEq
      have ordered := orderedTailDirections_eq_of_binary_profile
        routes clauseIndex copiedClause
        (⟨false, false⟩ : LiteralProfile)
        ⟨carrierLinkNextSlice retained link, true⟩
        (carrierLensRouteFirstDirection link.first.isHorizontal 1 0)
        (carrierLensRouteFirstDirection link.first.isHorizontal 1 1)
        firstTail secondTail binaryProfile lengthEq
        firstTailEq secondTailEq
      cases horizontal : link.first.isHorizontal <;>
        simpa [retained, positionedClause, copiedClause, routes, horizontal,
          carrierLensRouteFirstDirection,
          AxisDirection.clockwiseRank] using ordered
  | true =>
      have profileEq := input.routedProfile_eq_carrier
      have binaryProfile :
          DirectedClauseProfile.ofClause routes clauseIndex copiedClause =
            .binary ⟨false, true⟩
              (carrierLensRouteFirstDirection
                link.first.isHorizontal 0 0)
              ⟨carrierLinkNextSlice retained link, false⟩
              (carrierLensRouteFirstDirection
                link.first.isHorizontal 0 1) := by
        simpa [retained, positionedClause, copiedClause, routes,
          routedCopiedClauseProfile,
          BinaryRouteTailRecordFormatter.descriptorProfile,
          carrierClauseDescriptor] using profileEq
      have ordered := orderedTailDirections_eq_of_binary_profile
        routes clauseIndex copiedClause
        (⟨false, true⟩ : LiteralProfile)
        ⟨carrierLinkNextSlice retained link, false⟩
        (carrierLensRouteFirstDirection link.first.isHorizontal 0 0)
        (carrierLensRouteFirstDirection link.first.isHorizontal 0 1)
        firstTail secondTail binaryProfile lengthEq
        firstTailEq secondTailEq
      cases horizontal : link.first.isHorizontal <;>
        simpa [retained, positionedClause, copiedClause, routes, horizontal,
          carrierLensRouteFirstDirection,
          AxisDirection.clockwiseRank] using ordered

end PeriodicEightOccurrenceSplit
end LeanTrominoes

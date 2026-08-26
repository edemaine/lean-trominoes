/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairOwnershipData

/-! # Numeric semantics of rank-ordered carrier-pair ownership bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private theorem ownershipMagnitudesZero (shift : Cell) :
    ((decide
        (CarrierOwnershipShiftField.shiftValue
          .horizontalPositive shift = 0) &&
      decide
        (CarrierOwnershipShiftField.shiftValue
          .horizontalNegative shift = 0)) &&
      (decide
        (CarrierOwnershipShiftField.shiftValue
          .verticalPositive shift = 0) &&
      decide
        (CarrierOwnershipShiftField.shiftValue
          .verticalNegative shift = 0))) =
      decide (shift = (0, 0)) := by
  rcases shift with ⟨horizontal, vertical⟩
  cases horizontal <;> cases vertical <;>
    simp [CarrierOwnershipShiftField.shiftValue,
      CarrierOwnershipShiftField.horizontal,
      CarrierOwnershipShiftField.keepPositive]

private theorem getD_ownershipHorizontalPositive
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD
        Field.ownershipHorizontalPositive.index 0 =
      CarrierOwnershipShiftField.rankValue
        .horizontalPositive datum := by
  simpa [Field.index, CarrierOwnershipShiftField.index] using
    datum.scanUnaryFields_getD_ownershipShiftField
      CarrierOwnershipShiftField.Field.horizontalPositive

private theorem getD_ownershipHorizontalNegative
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD
        Field.ownershipHorizontalNegative.index 0 =
      CarrierOwnershipShiftField.rankValue
        .horizontalNegative datum := by
  simpa [Field.index, CarrierOwnershipShiftField.index] using
    datum.scanUnaryFields_getD_ownershipShiftField
      CarrierOwnershipShiftField.Field.horizontalNegative

private theorem getD_ownershipVerticalPositive
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD
        Field.ownershipVerticalPositive.index 0 =
      CarrierOwnershipShiftField.rankValue
        .verticalPositive datum := by
  simpa [Field.index, CarrierOwnershipShiftField.index] using
    datum.scanUnaryFields_getD_ownershipShiftField
      CarrierOwnershipShiftField.Field.verticalPositive

private theorem getD_ownershipVerticalNegative
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD
        Field.ownershipVerticalNegative.index 0 =
      CarrierOwnershipShiftField.rankValue
        .verticalNegative datum := by
  simpa [Field.index, CarrierOwnershipShiftField.index] using
    datum.scanUnaryFields_getD_ownershipShiftField
      CarrierOwnershipShiftField.Field.verticalNegative

private theorem ownershipRankValuesZero (datum : CarrierNodeRankDatum) :
    ((decide
        (CarrierOwnershipShiftField.rankValue
          .horizontalPositive datum = 0) &&
      decide
        (CarrierOwnershipShiftField.rankValue
          .horizontalNegative datum = 0)) &&
      (decide
        (CarrierOwnershipShiftField.rankValue
          .verticalPositive datum = 0) &&
      decide
        (CarrierOwnershipShiftField.rankValue
          .verticalNegative datum = 0))) =
      decide (datum.ownershipShift = (0, 0)) := by
  unfold CarrierOwnershipShiftField.rankValue
  exact ownershipMagnitudesZero datum.ownershipShift

/-- The four selected unary zero tests exactly recognize a zero ownership
shift at the requested endpoint of every ordered pair. -/
theorem endpointOwnershipZeroBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (side : UnaryFieldPairPresence.Side)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    endpointOwnershipZeroBits side
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide ((match side with
          | .first => first.1.ownershipShift
          | .second => second.1.ownershipShift) = (0, 0)) := by
  unfold endpointOwnershipZeroBits combined
  rw [fieldZeroBits_numericRouteDescriptors
      side .ownershipHorizontalPositive formula wellFormed degree isLocal
      forward nonempty,
    fieldZeroBits_numericRouteDescriptors
      side .ownershipHorizontalNegative formula wellFormed degree isLocal
      forward nonempty,
    fieldZeroBits_numericRouteDescriptors
      side .ownershipVerticalPositive formula wellFormed degree isLocal
      forward nonempty,
    fieldZeroBits_numericRouteDescriptors
      side .ownershipVerticalNegative formula wellFormed degree isLocal
      forward nonempty]
  change pairwise .conjunction
      (pairwise .conjunction _ _) (pairwise .conjunction _ _) = _
  rw [pairwise_matrix, pairwise_matrix, pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases side with
  | first =>
      simp only [UnarySmallSumBooleans.Operation.apply]
      rw [getD_ownershipHorizontalPositive first.1,
        getD_ownershipHorizontalNegative first.1,
        getD_ownershipVerticalPositive first.1,
        getD_ownershipVerticalNegative first.1]
      exact ownershipRankValuesZero first.1
  | second =>
      simp only [UnarySmallSumBooleans.Operation.apply]
      rw [getD_ownershipHorizontalPositive second.1,
        getD_ownershipHorizontalNegative second.1,
        getD_ownershipVerticalPositive second.1,
        getD_ownershipVerticalNegative second.1]
      exact ownershipRankValuesZero second.1

private theorem muxBits_matrix {Value : Type}
    (values : List Value)
    (selector whenTrue whenFalse : Value → Value → Bool) :
    muxBits
        (matrix values selector)
        (matrix values whenTrue)
        (matrix values whenFalse) =
      matrix values fun first second =>
        if selector first second then
          whenTrue first second
        else
          whenFalse first second := by
  unfold muxBits disjoined combined
  change pairwise .disjunction
      (pairwise .conjunction _ _)
      (pairwise .conjunction
        (AlignedBooleanListClosure.negated _) _) = _
  rw [negated_matrix, pairwise_matrix, pairwise_matrix, pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases selectorEq : selector first second <;>
    simp [selectorEq, UnarySmallSumBooleans.Operation.apply]

/-- The compiled ownership predicate follows the semantic endpoint priority
and therefore marks exactly the zero-owner representative pairs. -/
theorem representativeBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    representativeBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        first.1.pairIsRepresentative second.1 := by
  unfold representativeBits
  rw [firstBoundaryBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    secondBoundaryBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    show firstOwnershipZeroBits
        (PeriodicCNF.numericRouteDescriptors formula) = _ from
      endpointOwnershipZeroBits_numericRouteDescriptors .first
        formula wellFormed degree isLocal forward nonempty,
    show secondOwnershipZeroBits
        (PeriodicCNF.numericRouteDescriptors formula) = _ from
      endpointOwnershipZeroBits_numericRouteDescriptors .second
        formula wellFormed degree isLocal forward nonempty]
  rw [muxBits_matrix, muxBits_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases firstCrossingEq : first.1.boundaryCrossing <;>
    cases secondCrossingEq : second.1.boundaryCrossing <;>
      simp [CarrierNodeRankDatum.pairIsRepresentative,
        CarrierNodeRankDatum.pairRepresentativeShift,
        firstCrossingEq, secondCrossingEq]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

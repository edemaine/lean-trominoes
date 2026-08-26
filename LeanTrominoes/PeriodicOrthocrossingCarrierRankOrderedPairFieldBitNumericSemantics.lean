/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitData
import LeanTrominoes.UnaryFieldPairPresenceSemantics

/-! # Numeric semantics of rank-ordered carrier pair field bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private theorem fieldPresenceBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (side : UnaryFieldPairPresence.Side) (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldPresenceBits side field
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        UnaryFieldPairPresence.valuePresent side
          (first.1.scanUnaryFields.getD field.index 0)
          (second.1.scanUnaryFields.getD field.index 0) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have valuesEq := field.rankOrderedValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change field.rankOrderedValues descriptors =
    entries.map fun entry =>
      entry.1.scanUnaryFields.getD field.index 0 at valuesEq
  unfold fieldPresenceBits
  rw [valuesEq, UnaryFieldPairPresence.fieldBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

/-- Negating endpoint-field presence tests exactly whether the corresponding
unary natural is zero. -/
theorem fieldZeroBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (side : UnaryFieldPairPresence.Side) (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldZeroBits side field
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide ((match side with
          | .first => first.1.scanUnaryFields.getD field.index 0
          | .second => second.1.scanUnaryFields.getD field.index 0) = 0) := by
  unfold fieldZeroBits
  rw [fieldPresenceBits_numericRouteDescriptors side field
    formula wellFormed degree isLocal forward nonempty]
  rw [negated_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  have notPositiveIffZero (value : Nat) :
      (!decide (0 < value)) = decide (value = 0) := by
    cases value <;> simp
  cases side with
  | first =>
      simpa only [UnaryFieldPairPresence.valuePresent] using
        notPositiveIffZero
          (first.1.scanUnaryFields.getD field.index 0)
  | second =>
      simpa only [UnaryFieldPairPresence.valuePresent] using
        notPositiveIffZero
          (second.1.scanUnaryFields.getD field.index 0)

/-- The compiled first-endpoint presence bit of field eight is exactly the
horizontal-axis bit. -/
theorem axisBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    axisBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first _second => first.1.horizontal := by
  unfold axisBits
  rw [fieldPresenceBits_numericRouteDescriptors .first .horizontal
    formula wellFormed degree isLocal forward nonempty]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change UnaryFieldPairPresence.valuePresent .first
      (first.1.scanUnaryFields.getD 8 0)
      (second.1.scanUnaryFields.getD 8 0) = first.1.horizontal
  rw [CarrierNodeRankDatum.scanUnaryFields_getD_eight]
  cases first.1.horizontal <;> rfl

private theorem boundaryPresenceBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (side : UnaryFieldPairPresence.Side)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldPresenceBits side .boundaryPresence
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        match side with
        | .first => first.1.boundaryCrossing.isSome
        | .second => second.1.boundaryCrossing.isSome := by
  rw [fieldPresenceBits_numericRouteDescriptors side .boundaryPresence
    formula wellFormed degree isLocal forward nonempty]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change UnaryFieldPairPresence.valuePresent side
      (first.1.scanUnaryFields.getD 13 0)
      (second.1.scanUnaryFields.getD 13 0) = _
  rw [CarrierNodeRankDatum.scanUnaryFields_getD_thirteen,
    CarrierNodeRankDatum.scanUnaryFields_getD_thirteen]
  cases side <;>
    cases firstCrossingEq : first.1.boundaryCrossing <;>
      cases secondCrossingEq : second.1.boundaryCrossing <;>
        simp [UnaryFieldPairPresence.valuePresent,
          CarrierBoundaryPresenceField.rankValue,
          firstCrossingEq, secondCrossingEq]

theorem firstBoundaryBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    firstBoundaryBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first _second => first.1.boundaryCrossing.isSome := by
  exact boundaryPresenceBits_numericRouteDescriptors .first
    formula wellFormed degree isLocal forward nonempty

theorem secondBoundaryBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    secondBoundaryBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun _first second => second.1.boundaryCrossing.isSome := by
  exact boundaryPresenceBits_numericRouteDescriptors .second
    formula wellFormed degree isLocal forward nonempty

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

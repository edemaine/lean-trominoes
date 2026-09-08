/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingPlanarCrossovers
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Signed macrocell origins in global carrier order -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingMacroOrigin

open Computability Turing

abbrev Field := CarrierCrossingPointField.Field

/-- The physical crossing macrocell origin; terminals have a zero sentinel. -/
def nodeOrigin : CarrierNode → Cell
  | .terminal _ => (0, 0)
  | .boundary boundary => crossingMacroOrigin boundary.crossing

def nodeValue (field : Field) (node : CarrierNode) : Nat :=
  CarrierCrossingPointField.pointValue field (nodeOrigin node)

def compiledField : Field → CarrierRankDatumCompiledFields.Field
  | .horizontalPositive => .crossingPointHorizontalPositive
  | .horizontalNegative => .crossingPointHorizontalNegative
  | .verticalPositive => .crossingPointVerticalPositive
  | .verticalNegative => .crossingPointVerticalNegative

/-- Multiply the existing signed grid-point columns by the physical
macrocell scale, preserving their global carrier order. -/
def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  UnaryFieldConstantScale.values 20
    ((compiledField field).rankOrderedValues descriptors)

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      CarrierRankDatumCompiledFields.descriptorInputEncoding
      UnaryFieldEncoderMachine.unaryFields (values field) := by
  change TM2ComputableInPolyTime
    CarrierRankDatumCompiledFields.descriptorInputEncoding
    UnaryFieldEncoderMachine.unaryFields
    (fun descriptors => UnaryFieldConstantScale.values 20
      ((compiledField field).rankOrderedValues descriptors))
  exact TM2CompositionMachine.computableInPolyTime
    (compiledField field).rankOrderedValuesComputableInPolyTime
    (UnaryFieldConstantScale.computableInPolyTime 20)

private theorem toNat_twenty_mul (coordinate : Int) :
    (20 * coordinate).toNat = coordinate.toNat * 20 := by
  by_cases nonnegative : 0 ≤ coordinate
  · rw [Int.toNat_mul (by decide) nonnegative]
    simp [Nat.mul_comm]
  · have productNonpositive : 20 * coordinate ≤ 0 := by omega
    rw [Int.toNat_eq_zero.mpr productNonpositive,
      Int.toNat_eq_zero.mpr (by omega)]

/-- Signed magnitudes scale correctly even for negative translated nodes. -/
theorem nodeValue_eq_scaled (field : Field) (node : CarrierNode) :
    nodeValue field node = CarrierCrossingPointField.nodeValue field node * 20 := by
  cases node with
  | terminal terminal =>
      cases field <;> rfl
  | boundary boundary =>
      cases field <;>
        simp [nodeValue, nodeOrigin, crossingMacroOrigin,
          CarrierCrossingPointField.nodeValue,
          CarrierCrossingPointField.pointValue,
          CarrierCrossingPointField.horizontal,
          CarrierCrossingPointField.keepPositive,
          Cell.scale, planarMacroScale, ← mul_neg, toNat_twenty_mul]

private theorem compiledField_index (field : Field) :
    (compiledField field).index = CarrierCrossingPointField.index field := by
  cases field <;> rfl

/-- The actual retained physical nodes in the stable global carrier order. -/
def nodes (descriptors : List RouteDescriptor) : List CarrierNode :=
  let datums := (routeDescriptorCarrierRankDatumsAtPeriod
    (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  (CarrierRankGlobal.enumeration datums).map fun entry => entry.1.identity.node

/-- On numeric source routes, these unary columns are exactly the signed
coordinates of the physical crossing macrocell origins. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (field : Field) (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values field (PeriodicCNF.numericRouteDescriptors formula) =
      (nodes (PeriodicCNF.numericRouteDescriptors formula)).map (nodeValue field) := by
  unfold values UnaryFieldConstantScale.values
  rw [(compiledField field).rankOrderedValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  unfold nodes
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry entryMember
  have datumMember := List.fst_mem_of_mem_zipIdx
    ((CarrierRankGlobal.mem_enumeration_iff _ entry).mp entryMember)
  have originalMember := List.mem_dedup.mp datumMember
  rcases List.mem_map.mp originalMember with ⟨node, _nodeMember, datumEq⟩
  rw [compiledField_index,
    CarrierNodeRankDatum.scanUnaryFields_getD_crossingPointField,
    ← datumEq, CarrierCrossingPointField.rankValue_carrierNodeRankDatumAtPeriod]
  simp only [carrierNodeRankDatumAtPeriod, CarrierNodeCode.node_code]
  exact (nodeValue_eq_scaled field node).symm

end LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingMacroOrigin

end

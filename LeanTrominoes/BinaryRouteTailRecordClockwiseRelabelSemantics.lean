/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelData
import LeanTrominoes.BinaryRouteTailRecordFormatterData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorData

/-! # Semantics of clockwise binary route-tail relabeling -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordClockwiseRelabel

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

private theorem scan_tailBlock (swap : Bool)
    (slot : SourceLiteralSlot) (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition swap
        (tailBlock slot directions) =
      (swap, tailBlock (relabeledSourceSlot swap slot) directions) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change FiniteStateTransducer.scan transition swap
          (.direction slot direction :: tailBlock slot directions) =
        (swap, .direction (relabeledSourceSlot swap slot) direction ::
          tailBlock (relabeledSourceSlot swap slot) directions)
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

private theorem scan_binaryTailBody (swap : Bool)
    (first second : List AxisDirection) :
    FiniteStateTransducer.scan transition swap
        (tailBlock .first first ++
          tailBlock .second second ++ [.clauseEnd]) =
      (false,
        tailBlock (relabeledSourceSlot swap .first) first ++
          tailBlock (relabeledSourceSlot swap .second) second ++
          [.clauseEnd]) := by
  rw [show tailBlock .first first ++
          tailBlock .second second ++ [.clauseEnd] =
        tailBlock .first first ++
          (tailBlock .second second ++ [.clauseEnd]) by
        simp [List.append_assoc]]
  rw [FiniteStateTransducer.scan_append, scan_tailBlock]
  dsimp only
  rw [FiniteStateTransducer.scan_append, scan_tailBlock]
  simp [FiniteStateTransducer.scan, transition]

private theorem scan_clauseRecord_pair
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    FiniteStateTransducer.scan transition initial
        (clauseRecord profile [first, second]) =
      (false, relabeledBinaryClauseRecord profile first second) := by
  unfold clauseRecord
  simp only [taggedTailTokens, List.append_nil]
  rw [show (.profile profile ::
          (tailBlock .first first ++
            tailBlock .second second ++ [.clauseEnd])) =
        [.profile profile] ++
          (tailBlock .first first ++
            tailBlock .second second ++ [.clauseEnd]) by rfl]
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, transition]
  rw [scan_binaryTailBody]
  dsimp only
  by_cases swap : profileNeedsSwap profile = true
  · simp [relabeledBinaryClauseRecord, swap, relabeledSourceSlot,
      swapSourceSlot]
  · have noSwap : profileNeedsSwap profile = false :=
      Bool.eq_false_of_not_eq_true swap
    simp [relabeledBinaryClauseRecord, noSwap, relabeledSourceSlot,
      clauseRecord, taggedTailTokens, List.append_assoc]

/-- On a canonical two-tail clause record, the relabeler exchanges the two
finite source-slot tags exactly when the profile's clockwise order requires
it. -/
theorem output_clauseRecord_pair
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    output (clauseRecord profile [first, second]) =
      relabeledBinaryClauseRecord profile first second := by
  unfold output FiniteStateTransducer.output
  rw [scan_clauseRecord_pair]
  simp [finish]

@[simp] theorem profileNeedsSwap_carrier_forward
    (horizontal nextSlice : Bool) :
    profileNeedsSwap
        (BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor horizontal nextSlice true)) = true := by
  cases horizontal <;> cases nextSlice <;>
    native_decide

@[simp] theorem profileNeedsSwap_carrier_backward
    (horizontal nextSlice : Bool) :
    profileNeedsSwap
        (BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor horizontal nextSlice false)) =
      horizontal := by
  cases horizontal <;> cases nextSlice <;>
    native_decide

end BinaryRouteTailRecordClockwiseRelabel
end LeanTrominoes

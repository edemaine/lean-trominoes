/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelSemantics

/-! # Decoded semantics of clockwise binary route-tail relabeling -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordClockwiseRelabel

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

private theorem decoderScan_tailBlock (index : HeaderIndex)
    (selected : Option
      FormulaShapeFigureNinePolarityRouteHeader.Header)
    (sourceSlot : SourceLiteralSlot)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan
        (HorizontalRoutedRouteTailRecord.transition index) selected
        (tailBlock sourceSlot directions) =
      (selected,
        match selected with
        | none => []
        | some header =>
            if inheritedSourceSlot? header = some sourceSlot then
              directions.map
                HorizontalRoutedRouteHeaderTail.Token.tailDirection
            else []) := by
  induction directions with
  | nil =>
      cases selected <;>
        simp [tailBlock, FiniteStateTransducer.scan]
  | cons direction directions ih =>
      change FiniteStateTransducer.scan
          (HorizontalRoutedRouteTailRecord.transition index) selected
          (.direction sourceSlot direction ::
            tailBlock sourceSlot directions) = _
      cases selected with
      | none =>
          simp only [FiniteStateTransducer.scan,
            HorizontalRoutedRouteTailRecord.transition]
          rw [ih]
          simp
      | some header =>
          by_cases matchEq :
              inheritedSourceSlot? header = some sourceSlot <;>
            simp [FiniteStateTransducer.scan,
              HorizontalRoutedRouteTailRecord.transition,
              ih, matchEq]

private theorem decoderScan_swappedTailRecord (index : HeaderIndex)
    (selected : Option
      FormulaShapeFigureNinePolarityRouteHeader.Header)
    (first second : List AxisDirection) :
    FiniteStateTransducer.scan
        (HorizontalRoutedRouteTailRecord.transition index) selected
        (tailBlock .second first ++
          tailBlock .first second ++ [.clauseEnd]) =
      (none,
        match selected with
        | none => []
        | some header =>
            (selectedTailDirections [second, first] header).map
                HorizontalRoutedRouteHeaderTail.Token.tailDirection ++
              [.recordEnd]) := by
  rcases selected with _ | header
  · simp [FiniteStateTransducer.scan_append, decoderScan_tailBlock,
      FiniteStateTransducer.scan,
      HorizontalRoutedRouteTailRecord.transition]
  · rcases header with ⟨polarity, figurePrefix⟩
    cases figurePrefix with
    | «local» query =>
        simp [FiniteStateTransducer.scan_append, decoderScan_tailBlock,
          FiniteStateTransducer.scan,
          HorizontalRoutedRouteTailRecord.transition,
          selectedTailDirections, inheritedSourceSlot?]
    | inherited sourceSlot query =>
        cases sourceSlot <;>
          simp [FiniteStateTransducer.scan_append, decoderScan_tailBlock,
            FiniteStateTransducer.scan,
            HorizontalRoutedRouteTailRecord.transition,
            selectedTailDirections, inheritedSourceSlot?, sourceSlotNat,
            List.append_assoc]

private theorem decoderScan_swappedClauseRecord (index : HeaderIndex)
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    FiniteStateTransducer.scan
        (HorizontalRoutedRouteTailRecord.transition index) none
        (.profile profile ::
          (tailBlock .second first ++
            tailBlock .first second ++ [.clauseEnd])) =
      (none, optionRecord [second, first] (header? profile index)) := by
  rw [show (.profile profile ::
          (tailBlock .second first ++
            tailBlock .first second ++ [.clauseEnd])) =
        [.profile profile] ++
          (tailBlock .second first ++
            tailBlock .first second ++ [.clauseEnd]) by rfl]
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan,
    HorizontalRoutedRouteTailRecord.transition]
  rw [decoderScan_swappedTailRecord]
  cases lookup : header? profile index with
  | none => simp [optionRecord]
  | some header =>
      simp [optionRecord, HorizontalRoutedRouteHeaderTail.record]

private theorem indexedOutput_swappedClauseRecord (index : HeaderIndex)
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    indexedOutput index
        (.profile profile ::
          (tailBlock .second first ++
            tailBlock .first second ++ [.clauseEnd])) =
      optionRecord [second, first] (header? profile index) := by
  unfold indexedOutput FiniteStateTransducer.output
  rw [decoderScan_swappedClauseRecord]
  simp [HorizontalRoutedRouteTailRecord.finish]

private theorem expandedRecords_swappedClauseRecord
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    expandedRecords
        (.profile profile ::
          (tailBlock .second first ++
            tailBlock .first second ++ [.clauseEnd])) =
      sourceClauseRecords profile [second, first] := by
  calc
    expandedRecords
          (.profile profile ::
            (tailBlock .second first ++
              tailBlock .first second ++ [.clauseEnd])) =
        expandedRecords (clauseRecord profile [second, first]) := by
      unfold expandedRecords
      apply List.flatMap_congr
      intro index _indexMember
      rw [indexedOutput_swappedClauseRecord,
        indexedOutput_clauseRecord]
    _ = sourceClauseRecords profile [second, first] :=
      expandedRecords_clauseRecord profile [second, first]

/-- Decoding a relabeled binary record gives the semantic tail table in
clockwise source-slot order. -/
@[simp] theorem expandedRecords_relabeledBinaryClauseRecord
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    expandedRecords
        (relabeledBinaryClauseRecord profile first second) =
      sourceClauseRecords profile
        (if profileNeedsSwap profile then
          [second, first]
        else
          [first, second]) := by
  by_cases swap : profileNeedsSwap profile = true
  · simp only [relabeledBinaryClauseRecord, swap, if_pos]
    exact expandedRecords_swappedClauseRecord profile first second
  · have noSwap : profileNeedsSwap profile = false :=
      Bool.eq_false_of_not_eq_true swap
    simp only [relabeledBinaryClauseRecord, noSwap,
      Bool.false_eq_true, if_false]
    exact expandedRecords_clauseRecord profile [first, second]

/-- The finite-state relabeler therefore turns a canonical presentation-order
binary record into its exact clockwise decoded semantics. -/
@[simp] theorem expandedRecords_output_clauseRecord_pair
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    expandedRecords
        (output (clauseRecord profile [first, second])) =
      sourceClauseRecords profile
        (if profileNeedsSwap profile then
          [second, first]
        else
          [first, second]) := by
  rw [output_clauseRecord_pair,
    expandedRecords_relabeledBinaryClauseRecord]

end BinaryRouteTailRecordClockwiseRelabel
end LeanTrominoes

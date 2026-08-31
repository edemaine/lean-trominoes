/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelExpansionSemantics
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordBatchSemantics

/-! # Batched semantics of clockwise binary route-tail relabeling -/

namespace LeanTrominoes
namespace BinaryRouteTailRecordClockwiseRelabel

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

/-- Relabeled physical records for one four-route formatter block. -/
def relabeledBlockRecords
    (block : BinaryRouteTailRecordBatchFormatter.Block) : List Token :=
  relabeledBinaryClauseRecord block.firstProfile
      block.first.tail block.second.tail ++
    relabeledBinaryClauseRecord block.secondProfile
      block.third.tail block.fourth.tail

/-- Relabeled physical records for a stream of formatter blocks. -/
def relabeledRecords
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) : List Token :=
  blocks.flatMap relabeledBlockRecords

/-- Clockwise decoded semantics for one four-route formatter block. -/
def decodedBlockRecords
    (block : BinaryRouteTailRecordBatchFormatter.Block) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  sourceClauseRecords block.firstProfile
      (if profileNeedsSwap block.firstProfile then
        [block.second.tail, block.first.tail]
      else
        [block.first.tail, block.second.tail]) ++
    sourceClauseRecords block.secondProfile
      (if profileNeedsSwap block.secondProfile then
        [block.fourth.tail, block.third.tail]
      else
        [block.third.tail, block.fourth.tail])

/-- Clockwise decoded semantics for a stream of formatter blocks. -/
def decodedRecords
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  blocks.flatMap decodedBlockRecords

/-- Relabeling one complete canonical record before a remaining stream emits
one complete relabeled record and resumes from reset control. -/
theorem output_clauseRecord_pair_append
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection)
    (remaining : List Token) :
    output (clauseRecord profile [first, second] ++ remaining) =
      relabeledBinaryClauseRecord profile first second ++
        output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_clauseRecord_pair]
  simp [finish, initial]

/-- The formatter's canonical physical record stream relabels blockwise. -/
@[simp] theorem output_batchFormatter_records
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    output (BinaryRouteTailRecordBatchFormatter.records blocks) =
      relabeledRecords blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      change output
          (BinaryRouteTailRecordBatchFormatter.Block.records block ++
            BinaryRouteTailRecordBatchFormatter.records blocks) =
        relabeledBlockRecords block ++ relabeledRecords blocks
      unfold BinaryRouteTailRecordBatchFormatter.Block.records
        relabeledBlockRecords
      rw [show
          (clauseRecord block.firstProfile
                [block.first.tail, block.second.tail] ++
              clauseRecord block.secondProfile
                [block.third.tail, block.fourth.tail]) ++
              BinaryRouteTailRecordBatchFormatter.records blocks =
            clauseRecord block.firstProfile
                [block.first.tail, block.second.tail] ++
              (clauseRecord block.secondProfile
                  [block.third.tail, block.fourth.tail] ++
                BinaryRouteTailRecordBatchFormatter.records blocks) by
          simp [List.append_assoc]]
      rw [output_clauseRecord_pair_append,
        output_clauseRecord_pair_append]
      rw [induction]
      simp [List.append_assoc]

private def relabeledClauseBody
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) : List Token :=
  if profileNeedsSwap profile then
    .profile profile ::
      (tailBlock .second first ++ tailBlock .first second)
  else
    clauseBody profile [first, second]

private theorem relabeledBinaryClauseRecord_eq_body
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    relabeledBinaryClauseRecord profile first second =
      relabeledClauseBody profile first second ++ [.clauseEnd] := by
  by_cases swap : profileNeedsSwap profile = true
  · simp [relabeledBinaryClauseRecord, relabeledClauseBody, swap,
      List.append_assoc]
  · have noSwap : profileNeedsSwap profile = false :=
      Bool.eq_false_of_not_eq_true swap
    simp [relabeledBinaryClauseRecord, relabeledClauseBody, noSwap,
      clauseRecord_eq_body]

private theorem tailBlock_continues (sourceSlot : SourceLiteralSlot)
    (directions : List AxisDirection) :
    ∀ token ∈ tailBlock sourceSlot directions,
      isClauseEnd token = false := by
  intro token member
  obtain ⟨direction, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem relabeledClauseBody_continues
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection) :
    ∀ token ∈ relabeledClauseBody profile first second,
      isClauseEnd token = false := by
  by_cases swap : profileNeedsSwap profile = true
  · simp only [relabeledClauseBody, swap, if_pos]
    intro token member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · rfl
    · exact tailBlock_continues .second first token member
    · exact tailBlock_continues .first second token member
  · have noSwap : profileNeedsSwap profile = false :=
      Bool.eq_false_of_not_eq_true swap
    simp only [relabeledClauseBody, noSwap]
    exact clauseBody_continues profile [first, second]

private theorem blocksAux_relabeledBinaryClauseRecord_append
    (reverseBlock : List Token)
    (profile : DirectedClauseProfile)
    (first second : List AxisDirection)
    (remaining : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isClauseEnd reverseBlock
        (relabeledBinaryClauseRecord profile first second ++ remaining) =
      (reverseBlock.reverse ++
          relabeledBinaryClauseRecord profile first second) ::
        TM2EndDelimitedBlockMap.blocksAux isClauseEnd [] remaining := by
  rw [relabeledBinaryClauseRecord_eq_body, List.append_assoc]
  simpa [relabeledBinaryClauseRecord_eq_body, List.append_assoc] using
    blocksAux_append_clauseEnd reverseBlock
      (relabeledClauseBody profile first second) remaining
      (relabeledClauseBody_continues profile first second)

/-- Clause boundaries are unchanged, so splitting a relabeled block stream
recovers its two relabeled records per formatter block. -/
@[simp] theorem blocks_relabeledRecords
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    TM2EndDelimitedBlockMap.blocks isClauseEnd
        (relabeledRecords blocks) =
      blocks.flatMap fun block =>
        [relabeledBinaryClauseRecord block.firstProfile
            block.first.tail block.second.tail,
          relabeledBinaryClauseRecord block.secondProfile
            block.third.tail block.fourth.tail] := by
  unfold TM2EndDelimitedBlockMap.blocks relabeledRecords
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.flatMap_cons, relabeledBlockRecords]
      rw [show
          (relabeledBinaryClauseRecord block.firstProfile
                block.first.tail block.second.tail ++
              relabeledBinaryClauseRecord block.secondProfile
                block.third.tail block.fourth.tail) ++
              blocks.flatMap relabeledBlockRecords =
            relabeledBinaryClauseRecord block.firstProfile
                block.first.tail block.second.tail ++
              (relabeledBinaryClauseRecord block.secondProfile
                  block.third.tail block.fourth.tail ++
                blocks.flatMap relabeledBlockRecords) by
          simp [List.append_assoc]]
      rw [blocksAux_relabeledBinaryClauseRecord_append,
        blocksAux_relabeledBinaryClauseRecord_append]
      simp only [List.reverse_nil, List.nil_append]
      rw [induction]
      rfl

/-- Batched expansion of relabeled formatter records gives exactly the
clockwise decoded semantics of every block. -/
@[simp] theorem batchedRecords_relabeledRecords
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    batchedRecords (relabeledRecords blocks) = decodedRecords blocks := by
  unfold batchedRecords TM2EndDelimitedBlockMap.mappedOutput decodedRecords
  rw [blocks_relabeledRecords, List.flatMap_assoc]
  apply List.flatMap_congr
  intro block _blockMember
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [expandedRecords_relabeledBinaryClauseRecord,
    expandedRecords_relabeledBinaryClauseRecord]
  rfl

/-- The complete formatter/relabeler/decoder composition has exact clockwise
block semantics. -/
@[simp] theorem batchedRecords_output_batchFormatter_records
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    batchedRecords
        (output (BinaryRouteTailRecordBatchFormatter.records blocks)) =
      decodedRecords blocks := by
  rw [output_batchFormatter_records, batchedRecords_relabeledRecords]

end BinaryRouteTailRecordClockwiseRelabel
end LeanTrominoes

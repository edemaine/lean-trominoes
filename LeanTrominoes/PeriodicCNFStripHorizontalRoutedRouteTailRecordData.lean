/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.ListFinRangeGetElemPad
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData

/-! # Flat clause records for routed Figure 9 source tails -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteTailRecord

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

abbrev Header := FormulaShapeFigureNinePolarityRouteHeader.Header
abbrev OutputToken := HorizontalRoutedRouteHeaderTail.Token

/-- A flat source clause: its finite directed profile, followed by dynamic
tail directions explicitly tagged by clockwise source slot. -/
inductive Token
  | profile (value : DirectedClauseProfile)
  | direction (sourceSlot : SourceLiteralSlot) (value : AxisDirection)
  | clauseEnd
  deriving DecidableEq, Fintype, Inhabited

/-- Physical directions of one tagged dynamic tail. -/
def tailBlock (sourceSlot : SourceLiteralSlot)
    (directions : List AxisDirection) : List Token :=
  directions.map (Token.direction sourceSlot)

/-- Tag the first three dynamic tail rows by their stable clockwise slots.
Genuine width-three tables have no further rows. -/
def taggedTailTokens : List (List AxisDirection) → List Token
  | [] => []
  | first :: tails =>
      tailBlock .first first ++
        match tails with
        | [] => []
        | second :: tails =>
            tailBlock .second second ++
              match tails with
              | [] => []
              | third :: _ => tailBlock .third third

/-- Canonical flat input block for one directed source clause. -/
def clauseRecord (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) : List Token :=
  .profile profile :: (taggedTailTokens orderedTails ++ [.clauseEnd])

/-- Every finite source profile generates at most forty-three final polarity
headers.  This exact finite bound is discharged over the descriptor alphabet. -/
theorem sourceClauseHeaders_length_le :
    ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).length ≤ 43 := by
  native_decide

abbrev HeaderIndex := Fin 43

/-- Total bounded lookup for the header emitted by one fixed scan. -/
def header? (profile : DirectedClauseProfile)
    (index : HeaderIndex) : Option Header :=
  (sourceClauseHeaders profile)[index.val]?

/-- The dynamic source slot consumed by one finite header, if any. -/
def inheritedSourceSlot? (header : Header) : Option SourceLiteralSlot :=
  match header.figurePrefix with
  | .local _ => none
  | .inherited sourceSlot _ => some sourceSlot

/-- One fixed header-index scan stores only the selected finite header. -/
def transition (index : HeaderIndex) (selected : Option Header) :
    Token → Option Header × List OutputToken
  | .profile profile =>
      let current := header? profile index
      (current, current.toList.map
        HorizontalRoutedRouteHeaderTail.Token.header)
  | .direction sourceSlot direction =>
      (selected,
        match selected with
        | none => []
        | some header =>
            if inheritedSourceSlot? header = some sourceSlot then
              [.tailDirection direction]
            else [])
  | .clauseEnd =>
      (none, if selected.isSome then [.recordEnd] else [])

def finish (_ : Option Header) : List OutputToken := []

/-- Output of one fixed bounded header-index scan. -/
def indexedOutput (index : HeaderIndex) (input : List Token) :
    List OutputToken :=
  FiniteStateTransducer.output none (transition index) finish input

/-- Optional serialization of one selected header. -/
def optionRecord (orderedTails : List (List AxisDirection)) :
    Option Header → List OutputToken
  | none => []
  | some header =>
      HorizontalRoutedRouteHeaderTail.record header
        (selectedTailDirections orderedTails header)

private theorem scan_tailBlock (index : HeaderIndex)
    (selected : Option Header) (sourceSlot : SourceLiteralSlot)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan (transition index) selected
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
  | cons direction directions induction =>
      change FiniteStateTransducer.scan (transition index) selected
          (.direction sourceSlot direction ::
            tailBlock sourceSlot directions) = _
      cases selected with
      | none =>
          simp only [FiniteStateTransducer.scan, transition]
          rw [induction]
          simp
      | some header =>
          by_cases matchEq :
              inheritedSourceSlot? header = some sourceSlot <;>
            simp [FiniteStateTransducer.scan, transition, induction, matchEq]

private theorem scan_taggedTailTokens (index : HeaderIndex)
    (selected : Option Header)
    (orderedTails : List (List AxisDirection)) :
    FiniteStateTransducer.scan (transition index) selected
        (taggedTailTokens orderedTails) =
      (selected,
        match selected with
        | none => []
        | some header =>
            (selectedTailDirections orderedTails header).map
              HorizontalRoutedRouteHeaderTail.Token.tailDirection) := by
  rcases selected with _ | header
  · cases orderedTails with
    | nil => rfl
    | cons first tails =>
        cases tails with
        | nil =>
            simp [taggedTailTokens, scan_tailBlock]
        | cons second tails =>
            cases tails with
            | nil =>
                simp [taggedTailTokens, FiniteStateTransducer.scan_append,
                  scan_tailBlock]
            | cons third tails =>
                simp [taggedTailTokens, FiniteStateTransducer.scan_append,
                  scan_tailBlock]
  · rcases header with ⟨polarity, figurePrefix⟩
    cases figurePrefix with
    | «local» query =>
        cases orderedTails with
        | nil => rfl
        | cons first tails =>
            cases tails with
            | nil =>
                simp [taggedTailTokens, scan_tailBlock, selectedTailDirections,
                  inheritedSourceSlot?]
            | cons second tails =>
                cases tails with
                | nil =>
                    simp [taggedTailTokens,
                      FiniteStateTransducer.scan_append, scan_tailBlock,
                      selectedTailDirections, inheritedSourceSlot?]
                | cons third tails =>
                    simp [taggedTailTokens,
                      FiniteStateTransducer.scan_append, scan_tailBlock,
                      selectedTailDirections, inheritedSourceSlot?]
    | inherited sourceSlot query =>
        cases sourceSlot <;>
          cases orderedTails with
          | nil => rfl
          | cons first tails =>
              cases tails with
              | nil =>
                  simp [taggedTailTokens, scan_tailBlock,
                    selectedTailDirections, inheritedSourceSlot?,
                    sourceSlotNat]
              | cons second tails =>
                  cases tails with
                  | nil =>
                      simp [taggedTailTokens,
                        FiniteStateTransducer.scan_append, scan_tailBlock,
                        selectedTailDirections, inheritedSourceSlot?,
                        sourceSlotNat]
                  | cons third tails =>
                      simp [taggedTailTokens,
                        FiniteStateTransducer.scan_append, scan_tailBlock,
                        selectedTailDirections, inheritedSourceSlot?,
                        sourceSlotNat]

private theorem scan_tailRecord (index : HeaderIndex)
    (selected : Option Header)
    (orderedTails : List (List AxisDirection)) :
    FiniteStateTransducer.scan (transition index) selected
        (taggedTailTokens orderedTails ++ [.clauseEnd]) =
      (none,
        match selected with
        | none => []
        | some header =>
            (selectedTailDirections orderedTails header).map
                HorizontalRoutedRouteHeaderTail.Token.tailDirection ++
              [.recordEnd]) := by
  rw [FiniteStateTransducer.scan_append, scan_taggedTailTokens]
  cases selected <;>
    simp [FiniteStateTransducer.scan, transition]

private theorem scan_profile (index : HeaderIndex)
    (profile : DirectedClauseProfile) :
    FiniteStateTransducer.scan (transition index) none [.profile profile] =
      (header? profile index,
        (header? profile index).toList.map
          HorizontalRoutedRouteHeaderTail.Token.header) := by
  simp [FiniteStateTransducer.scan, transition]

private theorem scan_clauseRecord (index : HeaderIndex)
    (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    FiniteStateTransducer.scan (transition index) none
        (clauseRecord profile orderedTails) =
      (none, optionRecord orderedTails (header? profile index)) := by
  unfold clauseRecord
  rw [show (.profile profile ::
        (taggedTailTokens orderedTails ++ [.clauseEnd])) =
      [.profile profile] ++
        (taggedTailTokens orderedTails ++ [.clauseEnd]) by rfl]
  rw [FiniteStateTransducer.scan_append]
  simp only [scan_profile]
  rw [scan_tailRecord]
  cases lookup : header? profile index with
  | none => simp [optionRecord]
  | some header =>
      simp [optionRecord,
        HorizontalRoutedRouteHeaderTail.record]

/-- One bounded scan emits exactly its optional canonical header/tail record. -/
@[simp] theorem indexedOutput_clauseRecord (index : HeaderIndex)
    (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    indexedOutput index (clauseRecord profile orderedTails) =
      optionRecord orderedTails (header? profile index) := by
  unfold indexedOutput FiniteStateTransducer.output
  rw [scan_clauseRecord]
  simp [finish]

/-- Run every possible header index in increasing order. -/
def expandedRecords (input : List Token) : List OutputToken :=
  (List.finRange 43).flatMap fun index => indexedOutput index input

/-- The forty-three bounded scans reconstruct exactly the established
header/tail records for one canonical source clause. -/
@[simp] theorem expandedRecords_clauseRecord
    (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    expandedRecords (clauseRecord profile orderedTails) =
      sourceClauseRecords profile orderedTails := by
  let headers := sourceClauseHeaders profile
  have padded := List.map_finRange_getElem?_eq_pad headers 43
    (sourceClauseHeaders_length_le profile)
  unfold expandedRecords
  simp_rw [indexedOutput_clauseRecord]
  rw [← List.flatMap_map, show
      (List.finRange 43).map (fun index => header? profile index) =
        headers.map some ++ List.replicate (43 - headers.length) none by
      simpa only [header?, headers] using padded]
  rw [List.flatMap_append]
  have noneRecords :
      (List.replicate (43 - headers.length) none).flatMap
          (optionRecord orderedTails) = [] := by
    simp [optionRecord]
  rw [noneRecords, List.append_nil]
  unfold sourceClauseRecords sourceClausePairs
    HorizontalRoutedRouteHeaderTail.records
  rw [List.flatMap_map, List.flatMap_map]
  rfl

end HorizontalRoutedRouteTailRecord
end PeriodicCNFStripReduction
end LeanTrominoes

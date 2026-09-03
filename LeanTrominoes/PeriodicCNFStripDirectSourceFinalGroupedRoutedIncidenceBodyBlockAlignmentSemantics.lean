/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceBodySelectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceBodyAlignmentSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyBlockSemantics

/-! # Occurrence-block alignment of routed-incidence bodies -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

private theorem forall₂_map_eq_of_flatten_eq
    {First Output : Type*}
    (transform : First → Output) (width : Nat)
    (first : List (List First)) (second : List (List Output))
    (outerLength : first.length = second.length)
    (firstWidths : ∀ block ∈ first, block.length = width)
    (secondWidths : ∀ block ∈ second, block.length = width)
    (flattenEq : first.flatten.map transform = second.flatten) :
    List.Forall₂ (fun firstBlock secondBlock =>
      firstBlock.map transform = secondBlock) first second := by
  induction first generalizing second with
  | nil =>
      cases second <;> simp_all
  | cons firstBlock first induction =>
      cases second with
      | nil => simp at outerLength
      | cons secondBlock second =>
          have firstWidth : firstBlock.length = width :=
            firstWidths firstBlock (by simp)
          have secondWidth : secondBlock.length = width :=
            secondWidths secondBlock (by simp)
          have headEq := congrArg (List.take width) flattenEq
          have tailEq := congrArg (List.drop width) flattenEq
          simp only [List.flatten_cons, List.map_append] at headEq tailEq
          have headEq' : firstBlock.map transform = secondBlock := by
            simpa [firstWidth, secondWidth] using headEq
          have tailEq' : first.flatten.map transform = second.flatten := by
            simpa [firstWidth, secondWidth] using tailEq
          refine .cons headEq' (induction second ?_ ?_ ?_ tailEq')
          · simpa using outerLength
          · intro block blockMember
            exact firstWidths block (by simp [blockMember])
          · intro block blockMember
            exact secondWidths block (by simp [blockMember])

private theorem routedKeyBlocks_width
    (starts : List Nat) (data : List FinalFanOccurrenceData) :
    ∀ block ∈ List.zipWith
        (fun start datum =>
          (directFinalOccurrenceRoutedIncidenceKeyOffsets datum).map
            fun offset => start * 3 + offset)
        starts data,
      block.length = 3 := by
  induction starts generalizing data with
  | nil => simp
  | cons start starts induction =>
      cases data with
      | nil => simp
      | cons datum data =>
          intro block blockMember
          simp only [List.zipWith_cons_cons, List.mem_cons] at blockMember
          rcases blockMember with rfl | blockMember
          · simp
          · exact induction data block blockMember

private theorem directionBodyBlocks_width
    (frames : List DirectFinalOccurrenceFrame.Data)
    (pairs : List (HorizontalRoutedRouteHeaderTail.Header ×
      List AxisDirection)) :
    ∀ block ∈ List.zipWith directFinalOccurrenceDirectionBodyBlock
        frames pairs,
      block.length = 3 := by
  induction frames generalizing pairs with
  | nil => simp
  | cons frame frames induction =>
      cases pairs with
      | nil => simp
      | cons pair pairs =>
          intro current currentMember
          simp only [List.zipWith_cons_cons, List.mem_cons]
            at currentMember
          rcases currentMember with rfl | currentMember
          · exact directFinalOccurrenceDirectionBodyBlock_length _ _
          · exact induction pairs current currentMember

private theorem selectedBodyBlocks_width
    (indices : List Nat)
    (frames : List DirectFinalOccurrenceFrame.Data)
    (pairs : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection))
    (inRange : ∀ index ∈ indices,
      index < (List.zipWith directFinalOccurrenceDirectionBodyBlock
        frames pairs).length) :
    ∀ block ∈ indices.map fun index =>
        (List.zipWith directFinalOccurrenceDirectionBodyBlock
          frames pairs).getD index [],
      block.length = 3 := by
  intro block blockMember
  rcases List.mem_map.mp blockMember with ⟨index, indexMember, rfl⟩
  have indexLt := inRange index indexMember
  rw [List.getD_eq_getElem _ _ indexLt]
  exact directionBodyBlocks_width frames pairs _ (List.getElem_mem _)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- At every grouped occurrence ordinal, its three routed global keys map
to exactly the aligned RGB occurrence-body block selected by that ordinal. -/
theorem directSourceFinalGroupedRoutedIncidenceBodyBlocks_aligned
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun keyBlock bodyBlock =>
        keyBlock.map
          (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
            (directSourceFinalGroupedColoredOccurrenceDirectionBodies
              decider symbols)) = bodyBlock)
      (List.zipWith
        (fun start data =>
          (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
            fun offset => start * 3 + offset)
        (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
        (directSourceFinalGroupedOccurrenceData decider symbols))
      ((directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          (List.zipWith directFinalOccurrenceDirectionBodyBlock
            (directSourceFinalOccurrenceFramesExpected decider symbols)
            (directFigureNinePolarityRoutePairs decider symbols)).getD
              index []) := by
  let keyBlocks := List.zipWith
    (fun start data =>
      (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
        fun offset => start * 3 + offset)
    (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
    (directSourceFinalGroupedOccurrenceData decider symbols)
  let bodyBlocks :=
    (directSourceFinalGroupedOccurrenceIndices decider symbols).map
      fun index =>
        (List.zipWith directFinalOccurrenceDirectionBodyBlock
          (directSourceFinalOccurrenceFramesExpected decider symbols)
          (directFigureNinePolarityRoutePairs decider symbols)).getD index []
  let alignedBody := FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)
  apply forall₂_map_eq_of_flatten_eq alignedBody 3 keyBlocks bodyBlocks
  · dsimp [keyBlocks, bodyBlocks]
    simp
  · exact routedKeyBlocks_width _ _
  · apply selectedBodyBlocks_width
    intro index indexMember
    have groupedIndexLt := directSourceFinalGroupedOccurrenceIndex_lt
      decider symbols index indexMember
    have blocksLength :
        (List.zipWith directFinalOccurrenceDirectionBodyBlock
          (directSourceFinalOccurrenceFramesExpected decider symbols)
          (directFigureNinePolarityRoutePairs decider symbols)).length =
          (directSourceFinalCompiledOccurrenceData decider symbols).length := by
      rw [List.length_zipWith,
        directSourceFinalOccurrenceFramesExpected_length_eq_routePairs,
        min_self]
      have dataLength := congrArg List.length
        (directSourceFinalCompiledOccurrenceData_eq_routePairs decider symbols)
      simpa using dataLength.symm
    rw [blocksLength]
    exact groupedIndexLt
  · dsimp [keyBlocks, bodyBlocks, alignedBody]
    rw [← directSourceFinalGroupedRoutedIncidenceKeys_eq_occurrenceBlocks]
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    simp only [id_eq]
    rw [← directSourceFinalGroupedColoredOccurrenceDirectionBodies_eq_indexedBlocks]
    exact
      (directSourceFinalGroupedColoredOccurrenceDirectionBodies_eq_map_alignedBody
        decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end

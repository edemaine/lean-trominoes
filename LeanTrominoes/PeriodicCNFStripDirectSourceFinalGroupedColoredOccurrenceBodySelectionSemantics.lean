/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBodyBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairOccurrenceDataSemantics
import LeanTrominoes.PeriodicThreeDMNormalizationRasterizationCorrectness

/-! # Stable-index selection of grouped colored occurrence bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

private theorem alignedBody_range_eq_getD
    (bodies : List (List AxisDirection)) (index : Nat)
    (indexLt : index < bodies.length) :
    FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
        (List.range bodies.length) bodies index =
      bodies.getD index [] := by
  unfold FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
  have indexEq : (List.range bodies.length).idxOf index = index := by
    have rangeIndexLt : index < (List.range bodies.length).length := by
      simpa using indexLt
    have valueEq :
        (List.range bodies.length)[index]'rangeIndexLt = index :=
      List.getElem_range rangeIndexLt
    have indexEq := List.nodup_range.idxOf_getElem index rangeIndexLt
    rw [valueEq] at indexEq
    exact indexEq
  rw [indexEq]

private theorem zipWith_directionBodyBlocks_length
    (frames : List DirectFinalOccurrenceFrame.Data)
    (pairs : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    ∀ block ∈ List.zipWith directFinalOccurrenceDirectionBodyBlock
        frames pairs,
      block.length = 3 := by
  induction frames generalizing pairs with
  | nil => simp
  | cons frame frames induction =>
      cases pairs with
      | nil => simp
      | cons pair pairs =>
          intro block blockMember
          simp only [List.zipWith_cons_cons, List.mem_cons] at blockMember
          rcases blockMember with rfl | blockMember
          · exact directFinalOccurrenceDirectionBodyBlock_length frame pair
          · exact induction pairs block blockMember

private theorem three_getD_eq_self
    {Value : Type*} (values : List Value) (fallback : Value)
    (lengthEq : values.length = 3) :
    [values.getD 0 fallback, values.getD 1 fallback,
      values.getD 2 fallback] = values := by
  rcases values with _ | ⟨first, values⟩
  · simp at lengthEq
  rcases values with _ | ⟨second, values⟩
  · simp at lengthEq
  rcases values with _ | ⟨third, values⟩
  · simp at lengthEq
  rcases values with _ | ⟨fourth, values⟩
  · rfl
  · simp at lengthEq

private theorem three_positions_getD_flatten
    (blocks : List (List (List AxisDirection)))
    (blockLengths : ∀ block ∈ blocks, block.length = 3)
    (index : Nat) (indexLt : index < blocks.length) :
    [(blocks.flatten).getD (3 * index) [],
      (blocks.flatten).getD (3 * index + 1) [],
      (blocks.flatten).getD (3 * index + 2) []] =
      blocks.getD index [] := by
  have atOffset (offset : Nat) (offsetLt : offset < 3) :
      (blocks.flatten).getD (index * 3 + offset) [] =
        (blocks[index]).getD offset [] := by
    simpa using PeriodicThreeDM.List.getD_flatMap_fixedLength
      blocks id 3 index offset ([] : List AxisDirection)
      (fun block blockMember => blockLengths block blockMember)
      indexLt offsetLt
  have firstEq : (blocks.flatten).getD (3 * index) [] =
      (blocks[index]).getD 0 [] := by
    simpa [Nat.mul_comm] using atOffset 0 (by omega)
  have secondEq : (blocks.flatten).getD (3 * index + 1) [] =
      (blocks[index]).getD 1 [] := by
    simpa [Nat.mul_comm] using atOffset 1 (by omega)
  have thirdEq : (blocks.flatten).getD (3 * index + 2) [] =
      (blocks[index]).getD 2 [] := by
    simpa [Nat.mul_comm] using atOffset 2 (by omega)
  rw [firstEq, secondEq, thirdEq,
    List.getD_eq_getElem _ _ indexLt]
  exact three_getD_eq_self blocks[index] []
    (blockLengths blocks[index] (List.getElem_mem _))

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Grouping the three consecutive colored body ordinals at every stable
occurrence index selects exactly that occurrence's complete RGB body block. -/
theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBodies_eq_indexedBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).flatMap
        fun index =>
          (List.zipWith directFinalOccurrenceDirectionBodyBlock
            (directSourceFinalOccurrenceFramesExpected decider symbols)
            (directFigureNinePolarityRoutePairs decider symbols)).getD
              index [] := by
  let bodies := directSourceFinalColoredOccurrenceDirectionBodies
    decider symbols
  let ordinals :=
    directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
      decider symbols
  unfold directSourceFinalGroupedColoredOccurrenceDirectionBodies
  rw [FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList_eq_map_alignedBody
    (aligned := by simp)
    (keysNodup := List.nodup_range)
    (present := fun ordinal ordinalMember => List.mem_range.mpr
      (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinal_lt
        decider symbols ordinal ordinalMember))]
  have selectedEq :
      ordinals.map
          (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (List.range bodies.length) bodies) =
        ordinals.map fun ordinal => bodies.getD ordinal [] := by
    apply List.map_congr_left
    intro ordinal ordinalMember
    exact alignedBody_range_eq_getD bodies ordinal
      (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinal_lt
        decider symbols ordinal ordinalMember)
  change ordinals.map _ = _
  rw [selectedEq]
  rw [show ordinals =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).flatMap
        fun index => [3 * index, 3 * index + 1, 3 * index + 2] by
    exact directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_eq
      decider symbols]
  rw [show bodies =
      (List.zipWith directFinalOccurrenceDirectionBodyBlock
        (directSourceFinalOccurrenceFramesExpected decider symbols)
        (directFigureNinePolarityRoutePairs decider symbols)).flatten by
    exact directSourceFinalColoredOccurrenceDirectionBodies_eq_occurrenceBlocks
      decider symbols]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro index indexMember
  let blocks := List.zipWith directFinalOccurrenceDirectionBodyBlock
    (directSourceFinalOccurrenceFramesExpected decider symbols)
    (directFigureNinePolarityRoutePairs decider symbols)
  have blocksLength : blocks.length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    dsimp [blocks]
    rw [List.length_zipWith,
      directSourceFinalOccurrenceFramesExpected_length_eq_routePairs,
      min_self]
    have dataLength := congrArg List.length
      (directSourceFinalCompiledOccurrenceData_eq_routePairs decider symbols)
    simpa using dataLength.symm
  have indexLt : index < blocks.length := by
    rw [blocksLength]
    exact directSourceFinalGroupedOccurrenceIndex_lt
      decider symbols index indexMember
  change
    [(blocks.flatten).getD (3 * index) [],
      (blocks.flatten).getD (3 * index + 1) [],
      (blocks.flatten).getD (3 * index + 2) []] =
      blocks.getD index []
  exact three_positions_getD_flatten blocks
    (zipWith_directionBodyBlocks_length _ _) index indexLt

end LeanTrominoes.PeriodicCNFStripReduction

end

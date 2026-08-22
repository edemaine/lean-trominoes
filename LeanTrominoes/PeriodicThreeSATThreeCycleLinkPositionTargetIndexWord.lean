/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkTargetVertexIndexStream

/-! # Positional target-index words of cycle-link groups -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkDescriptorStreams

def groupTargetIndexWord (blockStart groupSize : Nat) : List Nat :=
  (List.range groupSize).flatMap fun position =>
    [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndex
        blockStart groupSize position,
      blockStart + position]

def targetIndexWordsAux : Nat → List Nat → List Nat
  | _, [] => []
  | blockStart, groupSize :: groupSizes =>
      groupTargetIndexWord blockStart groupSize ++
        targetIndexWordsAux (blockStart + groupSize) groupSizes

theorem interleaveWords_append
    {Value : Type*}
    (first second third fourth : List Value)
    (lengthEq : first.length = third.length) :
    interleaveWords (first ++ second) (third ++ fourth) =
      interleaveWords first third ++ interleaveWords second fourth := by
  induction first generalizing third with
  | nil =>
      have thirdNil : third = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst third
      rfl
  | cons firstValue first induction =>
      cases third with
      | nil => simp at lengthEq
      | cons thirdValue third =>
          have tailLength : first.length = third.length := by
            simpa using lengthEq
          unfold interleaveWords at induction ⊢
          simp only [List.cons_append, List.zip_cons_cons,
            List.flatMap_cons]
          rw [induction third tailLength]
          simp only [List.nil_append]

theorem interleaveWords_groupTargetIndices
    (blockStart groupSize : Nat) :
    interleaveWords
        (PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
          blockStart groupSize)
        ((List.range groupSize).map fun position =>
          blockStart + position) =
      groupTargetIndexWord blockStart groupSize := by
  simpa [PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices,
    groupTargetIndexWord] using
      interleaveWords_map (List.range groupSize)
        (PeriodicCNF.SourceCycleLinkTargetIndices.targetIndex
          blockStart groupSize)
        (fun position => blockStart + position)

theorem interleaveWords_targetIndicesAux
    (blockStart : Nat) (groupSizes : List Nat) :
    interleaveWords
        (PeriodicCNF.SourceCycleLinkTargetIndices.targetIndicesAux
          blockStart groupSizes)
        ((List.range groupSizes.sum).map fun index => blockStart + index) =
      targetIndexWordsAux blockStart groupSizes := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndicesAux,
        List.sum_cons,
        CycleLinkGroupedTargetIndices.map_range_add_split,
        interleaveWords_append _ _ _ _ (by simp),
        interleaveWords_groupTargetIndices,
        induction (blockStart + groupSize)]
      rfl

/-- The actual alternating incidence target indices are exactly the positional
target-index words consumed by successive emitter groups. -/
theorem cycleLinkIncidences_targetVertexIndices_eq_positionWords
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).map (fun incidence =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq incidence.literal.atom
          (rotatedOccurrenceVariables source)) =
      targetIndexWordsAux 0
        ((sourceVariables source).map fun atom =>
          (occurrenceVariables source atom).length) := by
  let groupSizes := (sourceVariables source).map fun atom =>
    (occurrenceVariables source atom).length
  have sizeEq : groupSizes.sum =
      PeriodicCNF.presentationLiteralCount source := by
    exact (occurrenceVariables_total_length source).trans
      (taggedLiterals_length source)
  have positional := interleaveWords_targetIndicesAux 0 groupSizes
  simp only [zero_add] at positional
  rw [sizeEq] at positional
  calc
    (cycleLinkIncidences source).map (fun incidence =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq incidence.literal.atom
          (rotatedOccurrenceVariables source)) =
        interleaveWords
          (PeriodicCNF.SourceCycleLinkTargetIndices.targetIndices groupSizes)
          (List.range (PeriodicCNF.presentationLiteralCount source)) := by
      exact cycleLinkIncidences_targetVertexIndices source
    _ = targetIndexWordsAux 0 groupSizes := by
      simpa [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndices]
        using positional

end CycleLinkDescriptorStreams
end PeriodicThreeSATThree
end LeanTrominoes

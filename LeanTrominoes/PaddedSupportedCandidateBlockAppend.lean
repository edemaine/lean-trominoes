/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Aligned concatenation of fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

variable {Index Value : Type*}

/-- Padded candidate construction distributes across an aligned prefix. -/
theorem candidates_append
    (firstActives secondActives : List Bool)
    (firstBlocks secondBlocks : List (List (Template Value)))
    (lengthEq : firstActives.length = firstBlocks.length) :
    candidates (firstActives ++ secondActives)
        (firstBlocks ++ secondBlocks) =
      candidates firstActives firstBlocks ++
        candidates secondActives secondBlocks := by
  induction firstActives generalizing firstBlocks with
  | nil =>
      have firstBlocksNil : firstBlocks = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst firstBlocks
      rfl
  | cons active actives induction =>
      cases firstBlocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          have tailLengthEq : actives.length = blocks.length := by
            simpa using lengthEq
          simp only [List.cons_append, candidates]
          rw [induction blocks tailLengthEq, List.append_assoc]

/-- Padded candidate construction distributes over an aligned flat-mapped
block family. -/
theorem candidates_flatMap
    (indices : List Index) (actives : Index → List Bool)
    (blocks : Index → List (List (Template Value)))
    (lengthEq : ∀ index ∈ indices,
      (actives index).length = (blocks index).length) :
    candidates (indices.flatMap actives) (indices.flatMap blocks) =
      indices.flatMap fun index =>
        candidates (actives index) (blocks index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      rw [candidates_append]
      · rw [induction]
        intro tailIndex tailMember
        exact lengthEq tailIndex
          (List.mem_cons_of_mem index tailMember)
      · exact lengthEq index (List.mem_cons_self)

/-- Compact active-value selection distributes across an aligned prefix. -/
theorem activeValues_append
    (firstActives secondActives : List Bool)
    (firstBlocks secondBlocks : List (List (Template Value)))
    (lengthEq : firstActives.length = firstBlocks.length) :
    activeValues (firstActives ++ secondActives)
        (firstBlocks ++ secondBlocks) =
      activeValues firstActives firstBlocks ++
        activeValues secondActives secondBlocks := by
  induction firstActives generalizing firstBlocks with
  | nil =>
      have firstBlocksNil : firstBlocks = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst firstBlocks
      rfl
  | cons active actives induction =>
      cases firstBlocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          have tailLengthEq : actives.length = blocks.length := by
            simpa using lengthEq
          simp only [List.cons_append, activeValues]
          rw [induction blocks tailLengthEq, List.append_assoc]

/-- Compact selection distributes over any aligned flat-mapped block
family. -/
theorem activeValues_flatMap
    (indices : List Index)
    (actives : Index → List Bool)
    (blocks : Index → List (List (Template Value)))
    (lengthEq : ∀ index ∈ indices,
      (actives index).length = (blocks index).length) :
    activeValues (indices.flatMap actives) (indices.flatMap blocks) =
      indices.flatMap fun index =>
        activeValues (actives index) (blocks index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      rw [activeValues_append]
      · rw [induction]
        intro tailIndex tailMember
        exact lengthEq tailIndex
          (List.mem_cons_of_mem index tailMember)
      · exact lengthEq index (List.mem_cons_self)

end LeanTrominoes.PaddedSupportedCandidateBlocks

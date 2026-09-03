/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexCompiler
import LeanTrominoes.ListZipWithFlatMapAligned

/-! # Zipping broadcast block indices with flattened blocks -/

namespace List

/-- If every block is nonempty, `FiniteBlockIndices.expectedAux` broadcasts
the same indices that `List.zipIdx` attaches to the blocks themselves. -/
theorem zipWith_expectedAux_flatten_eq_zipIdx_flatMap
    {Element Target : Type*}
    (combine : Nat → Element → Target)
    (start : Nat) (blocks : List (List Element))
    (blocksNonempty : ∀ block ∈ blocks, block ≠ []) :
    List.zipWith combine
        (LeanTrominoes.FiniteBlockIndices.expectedAux
          List.length start blocks)
        blocks.flatten =
      (blocks.zipIdx start).flatMap fun tagged =>
        tagged.1.map (combine tagged.2) := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block blocks induction =>
      have blockNonempty : block ≠ [] := blocksNonempty block (by simp)
      have tailNonempty : ∀ later ∈ blocks, later ≠ [] := by
        intro later member
        exact blocksNonempty later (by simp [member])
      have nextEq :
          LeanTrominoes.FiniteBlockIndices.nextIndex
              start block.length =
            start + 1 := by
        simp [LeanTrominoes.FiniteBlockIndices.nextIndex,
          blockNonempty]
      simp only [LeanTrominoes.FiniteBlockIndices.expectedAux,
        List.flatten_cons, List.zipIdx_cons, List.flatMap_cons]
      rw [List.zipWith_append_of_length_eq combine
        (List.replicate block.length start)
        (LeanTrominoes.FiniteBlockIndices.expectedAux
          List.length
          (LeanTrominoes.FiniteBlockIndices.nextIndex
            start block.length) blocks)
        block blocks.flatten (by simp),
        List.zipWith_replicate_left, nextEq,
        induction (start + 1) tailNonempty]

/-- Starting at zero, flattened elements inherit the ordinary `zipIdx`
index of their nonempty parent block. -/
theorem zipWith_expected_flatten_eq_zipIdx_flatMap
    {Element Target : Type*}
    (combine : Nat → Element → Target)
    (blocks : List (List Element))
    (blocksNonempty : ∀ block ∈ blocks, block ≠ []) :
    List.zipWith combine
        (LeanTrominoes.FiniteBlockIndices.expected List.length blocks)
        blocks.flatten =
      blocks.zipIdx.flatMap fun tagged =>
        tagged.1.map (combine tagged.2) := by
  exact zipWith_expectedAux_flatten_eq_zipIdx_flatMap
    combine 0 blocks blocksNonempty

/-- Explicitly broadcasting each `zipIdx` index across its block and then
zipping with the flattened blocks recovers the blockwise indexed map.  This
version also handles empty blocks because `zipIdx` advances unconditionally. -/
theorem zipWith_zipIdxReplicate_flatten_eq_zipIdx_flatMap
    {Element Target : Type*}
    (combine : Nat → Element → Target)
    (start : Nat) (blocks : List (List Element)) :
    List.zipWith combine
        ((blocks.zipIdx start).flatMap fun tagged =>
          List.replicate tagged.1.length tagged.2)
        blocks.flatten =
      (blocks.zipIdx start).flatMap fun tagged =>
        tagged.1.map (combine tagged.2) := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.zipIdx_cons, List.flatMap_cons,
        List.flatten_cons]
      rw [List.zipWith_append_of_length_eq combine
        (List.replicate block.length start)
        ((blocks.zipIdx (start + 1)).flatMap fun tagged =>
          List.replicate tagged.1.length tagged.2)
        block blocks.flatten (by simp),
        List.zipWith_replicate_left,
        induction (start + 1)]

/-- Zero-based specialization of
`zipWith_zipIdxReplicate_flatten_eq_zipIdx_flatMap`. -/
theorem zipWith_zipIdxReplicate_flatten_eq_zipIdx_flatMap_zero
    {Element Target : Type*}
    (combine : Nat → Element → Target)
    (blocks : List (List Element)) :
    List.zipWith combine
        (blocks.zipIdx.flatMap fun tagged =>
          List.replicate tagged.1.length tagged.2)
        blocks.flatten =
      blocks.zipIdx.flatMap fun tagged =>
        tagged.1.map (combine tagged.2) := by
  exact zipWith_zipIdxReplicate_flatten_eq_zipIdx_flatMap
    combine 0 blocks

end List

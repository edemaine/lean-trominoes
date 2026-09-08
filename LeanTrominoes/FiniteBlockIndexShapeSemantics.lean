/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteBlockIndexCompiler

/-! # Block indices depend only on block lengths -/

namespace LeanTrominoes.FiniteBlockIndices

/-- Broadcasting parent indices uses only the ordered block-length column. -/
theorem expectedAux_eq_lengths {Source : Type*}
    (blockLength : Source → Nat) (start : Nat) (source : List Source) :
    expectedAux blockLength start source =
      expectedAux id start (source.map blockLength) := by
  induction source generalizing start with
  | nil => rfl
  | cons item source induction =>
      simp only [expectedAux, List.map_cons, id_eq, induction]

/-- Any exact correspondence of block lengths preserves every emitted
parent index, including the handling of empty blocks. -/
theorem expected_eq_of_lengths {First Second : Type*}
    (firstLength : First → Nat) (secondLength : Second → Nat)
    (first : List First) (second : List Second)
    (lengths : first.map firstLength = second.map secondLength) :
    expected firstLength first = expected secondLength second := by
  unfold expected
  rw [expectedAux_eq_lengths firstLength 0 first,
    expectedAux_eq_lengths secondLength 0 second, lengths]

/-- With nonempty blocks, the emitted parent index is its actual source
position, repeated once per element of that block. -/
theorem expectedAux_eq_zipIdx_replicate {Source : Type*}
    (blockLength : Source → Nat) (start : Nat) (source : List Source)
    (positive : ∀ item ∈ source, 0 < blockLength item) :
    expectedAux blockLength start source =
      (source.zipIdx start).flatMap (fun tagged =>
        List.replicate (blockLength tagged.1) tagged.2) := by
  induction source generalizing start with
  | nil => rfl
  | cons item source induction =>
      have headPositive := positive item List.mem_cons_self
      have tailPositive : ∀ later ∈ source, 0 < blockLength later := by
        intro later member
        exact positive later (List.mem_cons_of_mem item member)
      simp only [expectedAux, nextIndex, Nat.ne_of_gt headPositive, if_false,
        List.zipIdx_cons, List.flatMap_cons]
      rw [induction (start + 1) tailPositive]

end LeanTrominoes.FiniteBlockIndices

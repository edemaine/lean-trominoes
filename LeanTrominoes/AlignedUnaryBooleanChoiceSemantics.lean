/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceCompiler

/-! # Semantics of aligned unary Boolean choice -/

namespace LeanTrominoes.AlignedUnaryBooleanChoice

/-- Declarative interleaving of two columns, truncated when either ends. -/
def interleaved : List Nat → List Nat → List Nat
  | first :: firsts, second :: seconds =>
      first :: second :: interleaved firsts seconds
  | _, _ => []

/-- Explicit query positions, starting at an arbitrary paired-field row. -/
def indexedQueriesAux : Nat → List Bool → List Nat
  | _, [] => []
  | start, control :: controls =>
      (start * 2 + BooleanListUnaryFields.bitNat control) ::
        indexedQueriesAux (start + 1) controls

private theorem sums_doubledRange
    (start : Nat) (controls : List Bool) :
    UnaryAlignedAddMachine.sums
        ((List.range' start controls.length).map fun index => index * 2)
        (BooleanListUnaryFields.values controls) =
      indexedQueriesAux start controls := by
  induction controls generalizing start with
  | nil =>
      simp [BooleanListUnaryFields.values, indexedQueriesAux,
        UnaryAlignedAddMachine.sums]
  | cons control controls induction =>
      rw [List.length_cons, List.range'_succ]
      simp only [List.map_cons, BooleanListUnaryFields.values,
        UnaryAlignedAddMachine.sums, indexedQueriesAux]
      change (start * 2 + BooleanListUnaryFields.bitNat control) ::
          UnaryAlignedAddMachine.sums
            ((List.range' (start + 1) controls.length).map
              fun index => index * 2)
            (BooleanListUnaryFields.values controls) =
        (start * 2 + BooleanListUnaryFields.bitNat control) ::
          indexedQueriesAux (start + 1) controls
      rw [induction]

/-- The compiled queries are exactly `2i` for false controls and `2i+1` for
true controls. -/
theorem queries_eq_indexedQueriesAux (controls : List Bool)
    (first : List Nat) (lengthEq : controls.length = first.length) :
    queries controls first = indexedQueriesAux 0 controls := by
  unfold queries AlignedUnaryListClosure.added doubledPositions
    UnaryFieldConstantScale.values UnaryFieldRange.values
  rw [← lengthEq]
  have rangeZero :
      List.range' 0 controls.length = List.range controls.length := by
    simp [List.range'_eq_map_range]
  rw [← rangeZero]
  exact sums_doubledRange 0 controls

/-- Alternating padding and aligned addition produce ordinary pairwise
interleaving. -/
theorem candidateValues_eq_interleaved (first second : List Nat) :
    candidateValues first second = interleaved first second := by
  induction first generalizing second with
  | nil =>
      simp [candidateValues, interleaved,
        UnaryFieldAlternatingPadding.appendZeroValues,
        UnaryFieldAlternatingPadding.prependZeroValues,
        AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums]
  | cons first firsts induction =>
      cases second with
      | nil =>
          simp [candidateValues, interleaved,
            UnaryFieldAlternatingPadding.appendZeroValues,
            UnaryFieldAlternatingPadding.prependZeroValues,
            AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums]
      | cons second seconds =>
          simp only [candidateValues,
            UnaryFieldAlternatingPadding.appendZeroValues,
            UnaryFieldAlternatingPadding.prependZeroValues,
            List.flatMap_cons, List.cons_append, List.nil_append,
            AlignedUnaryListClosure.added, UnaryAlignedAddMachine.sums,
            interleaved]
          rw [show
            UnaryAlignedAddMachine.sums
                (firsts.flatMap fun value => [value, 0])
                (seconds.flatMap fun value => [0, value]) =
              candidateValues firsts seconds by rfl]
          rw [induction]
          simp

private theorem indexedQueriesAux_forall_lt
    (start : Nat) (controls : List Bool) :
    (indexedQueriesAux start controls).Forall fun query =>
      query < (start + controls.length) * 2 := by
  induction controls generalizing start with
  | nil => simp [indexedQueriesAux]
  | cons control controls induction =>
      rw [indexedQueriesAux, List.forall_cons]
      constructor
      · cases control <;>
          simp [BooleanListUnaryFields.bitNat]
        <;> omega
      · have tail := induction (start + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

/-- Every compiled Boolean-choice query addresses its corresponding
two-field candidate row. -/
theorem queries_forall_lt_candidateValues_length
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length) :
    (queries controls first).Forall fun query =>
      query < (candidateValues first second).length := by
  rw [queries_eq_indexedQueriesAux controls first controlsFirst]
  have bounded := indexedQueriesAux_forall_lt 0 controls
  rw [candidateValues_length first second firstSecond]
  simpa [controlsFirst, Nat.mul_comm] using bounded

/-- On aligned inputs, the lookup implementation is ordinary zero-based
selection from the interleaved candidate column. -/
theorem selectedValues_eq_map_getD
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length) :
    selectedValues controls first second =
      (queries controls first).map fun query =>
        (candidateValues first second).getD query 0 := by
  unfold selectedValues
  apply UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt
  intro query queryMember
  exact (List.forall_iff_forall_mem.mp
    (queries_forall_lt_candidateValues_length
      controls first second controlsFirst firstSecond)) query queryMember

end LeanTrominoes.AlignedUnaryBooleanChoice

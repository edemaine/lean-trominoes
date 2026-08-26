/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsFirstTrueCompiler
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics

/-! # Semantics of keeping the first true equality position -/

namespace LeanTrominoes
namespace DelimitedBinaryWordsFirstTrue

variable {Value : Type*} [DecidableEq Value]

@[simp] theorem rowAux_true (bits : List Bool) :
    rowAux true bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;> simp [rowAux, induction, List.replicate_succ]

theorem equalityRow_eq_replicate_false_of_not_mem
    (values : List Value) (target : Value) (notMember : target ∉ values) :
    LastRepresentativeEqualityRows.equalityRow values target =
      List.replicate values.length false := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have targetNe : target ≠ value := by
        intro equal
        subst value
        exact notMember (by simp)
      have tailNotMember : target ∉ values := by
        intro member
        exact notMember (by simp [member])
      rw [show LastRepresentativeEqualityRows.equalityRow
            (value :: values) target =
          false :: LastRepresentativeEqualityRows.equalityRow values target by
        simp [LastRepresentativeEqualityRows.equalityRow, targetNe]]
      rw [induction tailNotMember]
      change false :: List.replicate values.length false =
        List.replicate (values.length + 1) false
      rw [List.replicate_succ]

/-- If the distinguished prefix contains a target exactly once, keeping only
the first true bit preserves its equality row and clears the entire suffix. -/
theorem row_equalityRow_append_of_nodup_mem
    (values suffix : List Value) (target : Value)
    (nodup : values.Nodup) (member : target ∈ values) :
    row (LastRepresentativeEqualityRows.equalityRow
        (values ++ suffix) target) =
      LastRepresentativeEqualityRows.equalityRow values target ++
        List.replicate suffix.length false := by
  induction values with
  | nil => simp at member
  | cons value values induction =>
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases same : target = value
      · subst value
        have targetNotTail := (List.nodup_cons.mp nodup).1
        rw [show LastRepresentativeEqualityRows.equalityRow
              ((target :: values) ++ suffix) target =
            true :: LastRepresentativeEqualityRows.equalityRow
              (values ++ suffix) target by
          simp [LastRepresentativeEqualityRows.equalityRow]]
        rw [show LastRepresentativeEqualityRows.equalityRow
              (target :: values) target =
            true :: LastRepresentativeEqualityRows.equalityRow
              values target by
          simp [LastRepresentativeEqualityRows.equalityRow]]
        unfold row
        simp only [rowAux]
        change true :: rowAux true
            (LastRepresentativeEqualityRows.equalityRow
              (values ++ suffix) target) = _
        rw [rowAux_true,
          equalityRow_eq_replicate_false_of_not_mem
            values target targetNotTail]
        have rowLength :
            (LastRepresentativeEqualityRows.equalityRow
              (values ++ suffix) target).length =
              values.length + suffix.length := by
          simp [LastRepresentativeEqualityRows.equalityRow]
        rw [rowLength]
        change true :: List.replicate
            (values.length + suffix.length) false =
          (true :: List.replicate values.length false) ++
            List.replicate suffix.length false
        rw [List.replicate_add]
        rfl
      · have tailMember : target ∈ values := by
          simpa [same] using member
        rw [show LastRepresentativeEqualityRows.equalityRow
              ((value :: values) ++ suffix) target =
            false :: LastRepresentativeEqualityRows.equalityRow
              (values ++ suffix) target by
          simp [LastRepresentativeEqualityRows.equalityRow, same]]
        rw [show LastRepresentativeEqualityRows.equalityRow
              (value :: values) target =
            false :: LastRepresentativeEqualityRows.equalityRow
              values target by
          simp [LastRepresentativeEqualityRows.equalityRow, same]]
        unfold row
        simp only [rowAux]
        simpa [row] using induction tailNodup tailMember

end DelimitedBinaryWordsFirstTrue
end LeanTrominoes

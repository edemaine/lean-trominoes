/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceSemantics
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler

/-! # Occurrence semantics of aligned unary Boolean choice -/

namespace LeanTrominoes.AlignedUnaryBooleanChoice

/-- Direct pointwise specification of Boolean choice between two aligned
columns. -/
def pointwiseSelected : List Bool → List Nat → List Nat → List Nat
  | control :: controls, first :: firsts, second :: seconds =>
      (if control then second else first) ::
        pointwiseSelected controls firsts seconds
  | _, _, _ => []

private theorem pointwiseSelected_length
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length) :
    (pointwiseSelected controls first second).length = controls.length := by
  induction controls generalizing first second with
  | nil => rfl
  | cons control controls induction =>
      cases first with
      | nil => simp at controlsFirst
      | cons first firsts =>
          cases second with
          | nil => simp at firstSecond
          | cons second seconds =>
              simp only [List.length_cons, Nat.succ.injEq] at controlsFirst firstSecond
              simp [pointwiseSelected,
                induction firsts seconds controlsFirst firstSecond]

private theorem pointwiseSelected_getD
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length)
    (index : Nat) (indexLt : index < controls.length) :
    (pointwiseSelected controls first second).getD index 0 =
      if controls.getD index false then
        second.getD index 0
      else first.getD index 0 := by
  induction controls generalizing first second index with
  | nil => simp at indexLt
  | cons control controls induction =>
      cases first with
      | nil => simp at controlsFirst
      | cons first firsts =>
          cases second with
          | nil => simp at firstSecond
          | cons second seconds =>
              have controlsFirstTail : controls.length = firsts.length := by
                simpa using Nat.succ.inj controlsFirst
              have firstSecondTail : firsts.length = seconds.length := by
                simpa using Nat.succ.inj firstSecond
              cases index with
              | zero => simp [pointwiseSelected]
              | succ index =>
                  have indexTail : index < controls.length := by
                    simpa using indexLt
                  simpa [pointwiseSelected] using
                    induction firsts seconds controlsFirstTail
                      firstSecondTail index indexTail

/-- The lookup-based compiler implements ordinary pointwise Boolean choice. -/
theorem selectedValues_eq_pointwiseSelected
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length) :
    selectedValues controls first second =
      pointwiseSelected controls first second := by
  apply List.ext_getElem
  · rw [selectedValues_length controls first second controlsFirst,
      pointwiseSelected_length controls first second controlsFirst firstSecond]
  · intro index selectedLt pointwiseLt
    have indexLt : index < controls.length := by
      simpa [selectedValues_length controls first second controlsFirst] using
        selectedLt
    rw [← List.getD_eq_getElem _ _ selectedLt,
      selectedValues_getD controls first second controlsFirst firstSecond
        index indexLt]
    rw [← pointwiseSelected_getD controls first second controlsFirst
      firstSecond index indexLt]
    exact List.getD_eq_getElem _ _ pointwiseLt

/-- Counting a target in the chosen column is the sum of its counts in the
false-selected first column and true-selected second column. -/
theorem selectedValues_count_eq_selected_branches
    (controls : List Bool) (first second : List Nat)
    (controlsFirst : controls.length = first.length)
    (firstSecond : first.length = second.length)
    (target : Nat) :
    (selectedValues controls first second).count target =
      (DelimitedBinaryWordBooleanFilter.selected
        (controls.map Bool.not) first).count target +
      (DelimitedBinaryWordBooleanFilter.selected
        controls second).count target := by
  rw [selectedValues_eq_pointwiseSelected controls first second
    controlsFirst firstSecond]
  induction controls generalizing first second with
  | nil => rfl
  | cons control controls induction =>
      cases first with
      | nil => simp at controlsFirst
      | cons first firsts =>
          cases second with
          | nil => simp at firstSecond
          | cons second seconds =>
              have controlsFirstTail : controls.length = firsts.length := by
                simpa using Nat.succ.inj controlsFirst
              have firstSecondTail : firsts.length = seconds.length := by
                simpa using Nat.succ.inj firstSecond
              have tailEq := induction firsts seconds
                controlsFirstTail firstSecondTail
              cases control with
              | false =>
                  simp [pointwiseSelected,
                    DelimitedBinaryWordBooleanFilter.selected]
                  simp only [List.count_cons]
                  rw [tailEq]
                  omega
              | true =>
                  simp [pointwiseSelected,
                    DelimitedBinaryWordBooleanFilter.selected]
                  simp only [List.count_cons]
                  rw [tailEq]
                  omega

end LeanTrominoes.AlignedUnaryBooleanChoice

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterData

/-! # Positional filtering of row-major binary-word pair matrices -/

namespace LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

theorem selectedPairs_append
    (firstControls secondControls : List Bool)
    (firstPairs secondPairs : List (List Bool × List Bool))
    (aligned : firstControls.length = firstPairs.length) :
    selectedPairs (firstControls ++ secondControls)
        (firstPairs ++ secondPairs) =
      selectedPairs firstControls firstPairs ++
        selectedPairs secondControls secondPairs := by
  induction firstControls generalizing firstPairs with
  | nil =>
      have firstPairsNil : firstPairs = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using aligned.symm)
      subst firstPairs
      rfl
  | cons control firstControls induction =>
      cases firstPairs with
      | nil => simp at aligned
      | cons pair firstPairs =>
          simp only [List.length_cons] at aligned
          simp only [List.cons_append, selectedPairs]
          split <;> simp [induction firstPairs (Nat.succ.inj aligned)]

theorem selectedPairs_map
    {Value : Type*} (values : List Value)
    (control : Value → Bool)
    (output : Value → List Bool × List Bool) :
    selectedPairs (values.map control) (values.map output) =
      values.filterMap fun value =>
        if control value then some (output value) else none := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, selectedPairs, List.filterMap_cons]
      split <;> simp [induction]

theorem selectedPairs_matrixRows
    {Value : Type*} (all rows : List Value)
    (control : Value → Value → Bool)
    (output : Value → List Bool) :
    selectedPairs
        (rows.flatMap fun first => all.map (control first))
        (rows.flatMap fun first => all.map fun second =>
          (output first, output second)) =
      rows.flatMap fun first =>
        all.filterMap fun second =>
          if control first second then
            some (output first, output second)
          else none := by
  induction rows with
  | nil => rfl
  | cons first rows induction =>
      simp only [List.flatMap_cons]
      rw [selectedPairs_append]
      · rw [selectedPairs_map, induction]
      · simp

theorem selectedPairs_matrix
    {Value : Type*} (values : List Value)
    (control : Value → Value → Bool)
    (output : Value → List Bool) :
    selectedPairs
        (values.flatMap fun first => values.map (control first))
        ((values.map output).flatMap fun first =>
          (values.map output).map fun second => (first, second)) =
      values.flatMap fun first =>
        values.filterMap fun second =>
          if control first second then
            some (output first, output second)
          else none := by
  simpa only [List.flatMap_map, List.map_map, Function.comp_def] using
    selectedPairs_matrixRows values values control output

end LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

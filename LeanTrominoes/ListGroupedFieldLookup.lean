/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListFilteredRankLookup

/-! # Aligned field selection preserves the order of each identity group -/

namespace List

/-- Selecting every matching identity index from an aligned field column
recovers exactly the filtered records' fields, in their original order. -/
theorem map_atomIndices_getD_eq_filter_map
    {Value Atom Field : Type*} [DecidableEq Atom]
    (values : List Value) (atomOf : Value → Atom) (atom : Atom)
    (field : Value → Field) (fallback : Field) :
    ((values.map atomOf).idxsOf atom).map
        (fun index => (values.map field).getD index fallback) =
      (values.filter (fun value => decide (atomOf value = atom))).map field := by
  have indices : (values.map atomOf).idxsOf atom =
      values.findIdxs (fun value => decide (atomOf value = atom)) := by
    simp only [idxsOf, findIdxs_map, Function.comp_def, Bool.beq_eq_decide_eq]
  rw [indices]
  apply List.ext_getElem
  · simp only [length_map, length_findIdxs, countP_eq_length_filter]
  · intro rank leftLt rightLt
    have rankLt : rank < (values.filter (fun value => decide (atomOf value = atom))).length := by
      simpa only [length_map] using rightLt
    have indexLt : rank < (values.findIdxs (fun value => decide (atomOf value = atom))).length := by
      simpa only [length_map] using leftLt
    have selected := filter_map_getD_eq_findIdxs_getD values
      (fun value => decide (atomOf value = atom)) field fallback rank rankLt
    rw [getD_eq_getElem _ _ rightLt, getD_eq_getElem _ _ indexLt] at selected
    simpa only [getElem_map] using selected.symm

/-- An exact correspondence of identity equality transports the complete
selected field group; numeric names need not coincide with semantic names. -/
theorem map_codeIndices_getD_eq_filter_map
    {Value Atom Field : Type*} [DecidableEq Atom]
    (values : List Value) (codeOf : Value → Nat) (code : Nat)
    (atomOf : Value → Atom) (atom : Atom)
    (field : Value → Field) (fallback : Field)
    (identified : ∀ value ∈ values, codeOf value = code ↔ atomOf value = atom) :
    ((values.map codeOf).idxsOf code).map
        (fun index => (values.map field).getD index fallback) =
      (values.filter (fun value => decide (atomOf value = atom))).map field := by
  rw [map_atomIndices_getD_eq_filter_map]
  apply congrArg (List.map field)
  apply filter_congr
  intro value member
  simp only [identified value member]

end List

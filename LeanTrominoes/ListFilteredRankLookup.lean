/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-! # Ranked filtered fields retain their original presentation indices -/

namespace List

/-- Looking up a field in a filtered list selects that same field at the
corresponding original presentation index. -/
theorem filter_map_getD_eq_findIdxs_getD
    {Value Field : Type*} (values : List Value) (predicate : Value → Bool)
    (field : Value → Field) (fallback : Field) (rank : Nat)
    (rankLt : rank < (values.filter predicate).length) :
    ((values.filter predicate).map field).getD rank fallback =
      (values.map field).getD ((values.findIdxs predicate).getD rank 0) fallback := by
  have rankIndexLt : rank < (values.findIdxs predicate).length := by
    simpa only [length_findIdxs, countP_eq_length_filter] using rankLt
  have selectedLt : (values.findIdxs predicate)[rank] < values.length := by
    simpa only [Nat.add_zero] using getElem_findIdxs_lt rankIndexLt
  rw [getD_eq_getElem _ _ (by simpa only [length_map] using rankLt), getElem_map,
    getD_eq_getElem _ _ rankIndexLt,
    getD_eq_getElem _ _ (by simpa only [length_map] using selectedLt), getElem_map]
  exact congrArg field (getElem_filter_eq_getElem_getElem_findIdxs rankLt)

/-- Atom-filtered field lookup can use the index list of the aligned atom
column, without reconstructing or reordering any field records. -/
theorem filter_map_getD_eq_atomIndices_getD
    {Value Atom Field : Type*} [DecidableEq Atom]
    (values : List Value) (atomOf : Value → Atom) (atom : Atom)
    (field : Value → Field) (fallback : Field) (rank : Nat)
    (rankLt : rank < (values.filter (fun value => decide (atomOf value = atom))).length) :
    ((values.filter (fun value => decide (atomOf value = atom))).map field).getD rank fallback =
      (values.map field).getD (((values.map atomOf).idxsOf atom).getD rank 0) fallback := by
  have indices : (values.map atomOf).idxsOf atom =
      values.findIdxs (fun value => decide (atomOf value = atom)) := by
    simp only [idxsOf, findIdxs_map, Function.comp_def, Bool.beq_eq_decide_eq]
  rw [indices]
  exact filter_map_getD_eq_findIdxs_getD values _ field fallback rank rankLt

end List

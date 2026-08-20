/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas

/-! # Generic identities for indexed list scans -/

namespace LeanTrominoes
namespace IndexedListScan

theorem idxOf_fst_eq_snd_of_mem_zipIdx
    {Value : Type} [DecidableEq Value]
    (values : List Value) (nodup : values.Nodup)
    (tagged : Value × Nat) (member : tagged ∈ values.zipIdx) :
    values.idxOf tagged.1 = tagged.2 := by
  have indexLt : tagged.2 < values.length :=
    List.snd_lt_of_mem_zipIdx member
  have valueEq : values[tagged.2] = tagged.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp member)).2
  rw [← valueEq]
  exact nodup.idxOf_getElem tagged.2 indexLt

/-- Push an indexed filter and output scan back through a pointwise map. -/
theorem map_zipIdx_filter_flatMap_congr
    {Value Position Output : Type}
    (values : List Value) (position : Value → Position)
    (selectedIndex : Nat → Bool) (selectedValue : Value → Bool)
    (output : Position → List Output)
    (selectedEq : ∀ tagged ∈ values.zipIdx,
      selectedIndex tagged.2 = selectedValue tagged.1) :
    (((values.map position).zipIdx.filter fun tagged =>
        selectedIndex tagged.2).flatMap fun tagged => output tagged.1) =
      ((values.zipIdx.filter fun tagged =>
        selectedValue tagged.1).flatMap fun tagged =>
          output (position tagged.1)) := by
  rw [List.zipIdx_map]
  simp only [List.filter_map, Function.comp_def, List.flatMap_map]
  congr 1
  apply List.filter_congr
  intro tagged member
  exact selectedEq tagged member

/-- If selection and output inspect only the value, stable indices can be
erased from the scan. -/
theorem zipIdx_filter_fst_flatMap
    {Value Output : Type}
    (values : List Value) (selected : Value → Bool)
    (output : Value → List Output) :
    ((values.zipIdx.filter fun tagged => selected tagged.1).flatMap
        fun tagged => output tagged.1) =
      (values.filter selected).flatMap output := by
  rw [← List.flatMap_map]
  congr 1
  change List.map Prod.fst
      (List.filter (selected ∘ Prod.fst) values.zipIdx) =
    List.filter selected values
  rw [← List.filter_map, List.zipIdx_map_fst]

end IndexedListScan
end LeanTrominoes

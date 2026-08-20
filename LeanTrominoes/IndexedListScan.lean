/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

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

/-- Indexing a flat map of fixed-width blocks is the same as indexing every
block at the affine offset determined by its outer stable index. -/
theorem flatMap_zipIdx_eq_zipIdx_flatMap_fixed
    {Value Output : Type}
    (values : List Value) (block : Value → List Output)
    (width start outerStart : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (values.flatMap block).zipIdx (start + width * outerStart) =
      (values.zipIdx outerStart).flatMap fun tagged =>
        (block tagged.1).zipIdx (start + width * tagged.2) := by
  induction values generalizing outerStart with
  | nil => simp
  | cons value values induction =>
      rw [List.flatMap_cons, List.zipIdx_append,
        List.zipIdx_cons, List.flatMap_cons]
      rw [blockLength value]
      have tail := induction (outerStart := outerStart + 1)
      rw [show start + width * outerStart + width =
          start + width * (outerStart + 1) by
            rw [Nat.mul_add, Nat.mul_one]
            omega,
        tail]

/-- Default-zero specialization of the fixed-width indexed flat-map law. -/
theorem flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
    {Value Output : Type}
    (values : List Value) (block : Value → List Output)
    (width start : Nat)
    (blockLength : ∀ value, (block value).length = width) :
    (values.flatMap block).zipIdx start =
      values.zipIdx.flatMap fun tagged =>
        (block tagged.1).zipIdx (start + width * tagged.2) := by
  simpa using flatMap_zipIdx_eq_zipIdx_flatMap_fixed
    values block width start 0 blockLength

/-- On a natural range, the outer value is already its stable index. -/
theorem range_flatMap_zipIdx_eq_flatMap_zipIdx_fixed
    {Output : Type}
    (count : Nat) (block : Nat → List Output)
    (width start : Nat)
    (blockLength : ∀ index, (block index).length = width) :
    ((List.range count).flatMap block).zipIdx start =
      (List.range count).flatMap fun index =>
        (block index).zipIdx (start + width * index) := by
  rw [flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
    (List.range count) block width start blockLength]
  have zipEq :
      (List.range count).zipIdx =
        (List.range count).map fun index => (index, index) := by
    apply List.ext_getElem
    · simp
    · intro index leftBound rightBound
      simp
  rw [zipEq, List.flatMap_map]

end IndexedListScan
end LeanTrominoes

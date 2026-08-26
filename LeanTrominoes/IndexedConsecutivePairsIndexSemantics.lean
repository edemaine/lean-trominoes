/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsData
import Mathlib.Data.List.Basic

/-! # Adjacent pairs characterized by list indices -/

namespace LeanTrominoes.IndexedConsecutivePairs

/-- In a duplicate-free list, two members are adjacent in the forward
direction exactly when the second index is the successor of the first. -/
theorem mem_pairs_iff_idxOf_eq_succ
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (valuesNodup : values.Nodup)
    (first second : Value) :
    (first, second) ∈ pairs values ↔
      first ∈ values ∧ second ∈ values ∧
        values.idxOf second = values.idxOf first + 1 := by
  constructor
  · intro pairMember
    simp only [pairs, List.mem_filterMap] at pairMember
    rcases pairMember with ⟨index, indexMember, pairLookup⟩
    have indexLt : index < values.length := List.mem_range.mp indexMember
    cases firstLookup : values[index]? with
    | none => simp [pairAt?, firstLookup] at pairLookup
    | some firstAt =>
        cases secondLookup : values[index + 1]? with
        | none => simp [pairAt?, firstLookup, secondLookup] at pairLookup
        | some secondAt =>
            simp [pairAt?, firstLookup, secondLookup] at pairLookup
            rcases pairLookup with ⟨firstEq, secondEq⟩
            subst first
            subst second
            have firstData := List.getElem?_eq_some_iff.mp firstLookup
            have secondData := List.getElem?_eq_some_iff.mp secondLookup
            have firstIndex : values.idxOf firstAt = index := by
              rw [← firstData.2]
              exact valuesNodup.idxOf_getElem index firstData.1
            have secondIndex : values.idxOf secondAt = index + 1 := by
              rw [← secondData.2]
              exact valuesNodup.idxOf_getElem (index + 1) secondData.1
            exact ⟨List.mem_of_getElem firstData.2,
              List.mem_of_getElem secondData.2, by omega⟩
  · rintro ⟨firstMember, secondMember, indexEq⟩
    simp only [pairs, List.mem_filterMap]
    refine ⟨values.idxOf first,
      List.mem_range.mpr (List.idxOf_lt_length_iff.mpr firstMember), ?_⟩
    have firstLookup := List.getElem?_idxOf firstMember
    have secondLookup := List.getElem?_idxOf secondMember
    unfold pairAt?
    rw [firstLookup]
    rw [show values.idxOf first + 1 = values.idxOf second by omega]
    rw [secondLookup]
    rfl

end LeanTrominoes.IndexedConsecutivePairs

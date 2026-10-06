/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace LeanTrominoes

/-- Boolean universal quantification without dependent membership witnesses. -/
def multisetAll {α : Type*} (items : Multiset α) (test : α → Bool) : Bool :=
  Quotient.liftOn items (fun xs => xs.all test) (by
    intro xs ys permutation
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun h x member => h x (permutation.mem_iff.mpr member),
      fun h x member => h x (permutation.mem_iff.mp member)⟩)

@[simp]
theorem multisetAll_eq_true {α : Type*} (items : Multiset α) (test : α → Bool) :
    multisetAll items test = true ↔ ∀ x ∈ items, test x = true := by
  induction items using Quotient.inductionOn
  simp [multisetAll]

/-- Boolean universal quantification over the actual finite enumeration. -/
def finiteAll {α : Type*} [Fintype α] (test : α → Bool) : Bool :=
  multisetAll (Finset.univ : Finset α).val test

@[simp]
theorem finiteAll_eq_true {α : Type*} [Fintype α] (test : α → Bool) :
    finiteAll test = true ↔ ∀ x, test x = true := by
  simp [finiteAll]

end LeanTrominoes

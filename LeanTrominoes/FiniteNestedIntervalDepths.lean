/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNestedIntervalRanks
import LeanTrominoes.FiniteOrderedRanks
import Mathlib.Data.Prod.Lex

/-! # Distinct bounded depths respecting proper interval nesting -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

def nestingKey {α : Type*} [LinearOrder α] (intervals : Finset (α × α))
    (interval : α × α) : Nat ×ₗ (α ×ₗ α) := toLex (nestingDepth intervals interval,toLex interval)

theorem nestingKey_injective {α : Type*} [LinearOrder α] (intervals : Finset (α × α)) :
    Function.Injective (nestingKey intervals) := by
  intro first second equal
  exact congrArg (fun key => ofLex (ofLex key).2) equal

def distinctNestingDepth {α : Type*} [LinearOrder α] (intervals : Finset (α × α))
    (interval : α × α) : Nat :=
  finiteOrderRank (intervals.image (nestingKey intervals)) (nestingKey intervals interval)

theorem distinctNestingDepth_positive {α : Type*} [LinearOrder α]
    (intervals : Finset (α × α)) (interval : α × α) :
    0 < distinctNestingDepth intervals interval := finiteOrderRank_positive _ _

theorem distinctNestingDepth_le_card {α : Type*} [LinearOrder α]
    {intervals : Finset (α × α)} {interval : α × α} (member : interval ∈ intervals) :
    distinctNestingDepth intervals interval ≤ intervals.card :=
  (finiteOrderRank_le_card (Finset.mem_image.mpr ⟨interval,member,rfl⟩)).trans
    (Finset.card_image_le)

theorem distinctNestingDepth_injective {α : Type*} [LinearOrder α]
    (intervals : Finset (α × α)) : Set.InjOn (distinctNestingDepth intervals) intervals := by
  intro first fm second sm equal
  apply nestingKey_injective intervals
  apply (finiteOrderRank_strictMonoOn (intervals.image (nestingKey intervals))).injOn
  · exact Finset.mem_image.mpr ⟨first,fm,rfl⟩
  · exact Finset.mem_image.mpr ⟨second,sm,rfl⟩
  · exact equal

theorem distinctNestingDepth_strict {α : Type*} [LinearOrder α]
    {intervals : Finset (α × α)} {outer inner : α × α}
    (outerMember : outer ∈ intervals) (innerMember : inner ∈ intervals)
    (firstOrder : outer.1 < inner.1) (lastOrder : inner.2 < outer.2) :
    distinctNestingDepth intervals inner < distinctNestingDepth intervals outer := by
  apply finiteOrderRank_strictMonoOn
  · exact Finset.mem_image.mpr ⟨inner,innerMember,rfl⟩
  · exact Finset.mem_image.mpr ⟨outer,outerMember,rfl⟩
  · apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inl (nestingDepth_strict outerMember firstOrder lastOrder)

end LeanTrominoes.OrthogonalBoundaryRouting

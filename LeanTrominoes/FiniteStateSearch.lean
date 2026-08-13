/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteState

/-!
# Bounded finite-state cycle search

Every cycle in a finite transition system can be shortened to a positive
cycle of length at most the number of states.  This file packages that
bounded certificate as a decidable predicate, providing the concrete search
bound used by the periodic-strip algorithm.
-/

namespace LeanTrominoes.FiniteState

/-- A directed cycle whose positive length is at most the number of states. -/
def HasBoundedCycle {α : Type*} [Fintype α]
    (relation : α → α → Prop) : Prop :=
  ∃ periodPred : Fin (Fintype.card α),
    ∃ states : Fin (periodPred.val + 1) → α,
      ∀ index, relation (states index) (states (index + 1))

instance {α : Type*} [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation] :
    Decidable (HasBoundedCycle relation) := by
  unfold HasBoundedCycle
  infer_instance

theorem hasCycle_of_hasBoundedCycle {α : Type*} [Fintype α]
    {relation : α → α → Prop}
    (bounded : HasBoundedCycle relation) : HasCycle relation := by
  obtain ⟨periodPred, states, step⟩ := bounded
  exact ⟨periodPred.val, states, step⟩

theorem hasBoundedCycle_of_path_repeat {α : Type*} [Fintype α]
    {relation : α → α → Prop}
    {path : Int → α} (step : IsBiInfinitePath relation path)
    {first second : Nat} (less : first < second)
    (secondBound : second < Fintype.card α + 1)
    (repeated : path first = path second) :
    HasBoundedCycle relation := by
  let distance := second - first
  have distancePositive : 0 < distance := by omega
  have distanceBound : distance - 1 < Fintype.card α := by omega
  have distanceSize : (distance - 1) + 1 = distance := by omega
  refine ⟨⟨distance - 1, distanceBound⟩,
    fun index => path (first + index.val), ?_⟩
  intro index
  change relation (path ((first : Int) + index.val))
    (path ((first : Int) + (index + 1).val))
  by_cases beforeEnd : index.val + 1 < distance
  · have nextValue : (index + 1).val = index.val + 1 := by
      simp [Fin.val_add, distanceSize, Nat.mod_eq_of_lt beforeEnd]
    rw [nextValue]
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      step (((first + index.val : Nat) : Int))
  · have atEnd : index.val + 1 = distance := by
      have indexBound : index.val < distance := by
        have bound := index.isLt
        change index.val < (distance - 1) + 1 at bound
        simpa only [distanceSize] using bound
      omega
    have nextValue : (index + 1).val = 0 := by
      simp [Fin.val_add, distanceSize, atEnd]
    rw [nextValue]
    have startAtLast : first + index.val = second - 1 := by
      dsimp [distance] at atEnd
      omega
    have lastStep := step (((second - 1 : Nat) : Int))
    convert lastStep using 1
    · congr 1
      exact_mod_cast startAtLast
    · have secondSub : second - 1 + 1 = second := by omega
      simp only [Nat.cast_zero, add_zero]
      rw [repeated]
      congr 1
      exact_mod_cast secondSub.symm

theorem hasBoundedCycle_of_hasBiInfinitePath {α : Type*} [Fintype α]
    {relation : α → α → Prop}
    (infinite : HasBiInfinitePath relation) : HasBoundedCycle relation := by
  obtain ⟨path, step⟩ := infinite
  let sample : Fin (Fintype.card α + 1) → α := fun index => path index.val
  obtain ⟨first, second, distinct, repeated⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt sample (by simp)
  have valueDistinct : first.val ≠ second.val := by
    intro equality
    exact distinct (Fin.ext equality)
  rcases Nat.lt_or_gt_of_ne valueDistinct with less | greater
  · exact hasBoundedCycle_of_path_repeat step less second.isLt repeated
  · exact hasBoundedCycle_of_path_repeat step greater first.isLt repeated.symm

theorem hasCycle_iff_hasBoundedCycle {α : Type*} [Fintype α]
    (relation : α → α → Prop) :
    HasCycle relation ↔ HasBoundedCycle relation := by
  constructor
  · intro cycle
    exact hasBoundedCycle_of_hasBiInfinitePath
      (hasBiInfinitePath_of_hasCycle cycle)
  · exact hasCycle_of_hasBoundedCycle

end LeanTrominoes.FiniteState

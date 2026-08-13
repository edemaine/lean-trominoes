/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalDrawing
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite transition systems

The 1.5D upper bound reduces strip tilings to paths through a finite system of
frontier states.  This file records the pumping fact needed by that reduction:
a finite transition system admits a bi-infinite path exactly when it contains
a nonempty directed cycle.
-/

namespace LeanTrominoes.FiniteState

/-- A path indexed in both directions whose successive states satisfy
`relation`. -/
def IsBiInfinitePath {α : Type*} (relation : α → α → Prop)
    (path : Int → α) : Prop :=
  ∀ index, relation (path index) (path (index + 1))

/-- Some path indexed by all integer positions follows `relation`. -/
def HasBiInfinitePath {α : Type*} (relation : α → α → Prop) : Prop :=
  ∃ path, IsBiInfinitePath relation path

/-- A nonempty directed cycle.  The successor on `Fin (periodPred + 1)` wraps
the final state back to the first. -/
def HasCycle {α : Type*} (relation : α → α → Prop) : Prop :=
  ∃ periodPred : Nat, ∃ states : Fin (periodPred + 1) → α,
    ∀ index, relation (states index) (states (index + 1))

/-- Repeating a directed cycle gives a bi-infinite path. -/
theorem hasBiInfinitePath_of_hasCycle {α : Type*}
    {relation : α → α → Prop}
    (cycle : HasCycle relation) : HasBiInfinitePath relation := by
  obtain ⟨periodPred, states, step⟩ := cycle
  refine ⟨fun index => states
    (Gadget.PeriodicOrthogonalDrawing.residue index periodPred), ?_⟩
  intro index
  change relation
    (states (Gadget.PeriodicOrthogonalDrawing.residue index periodPred))
    (states (Gadget.PeriodicOrthogonalDrawing.residue (index + 1) periodPred))
  rw [Gadget.PeriodicOrthogonalDrawing.residue_add_one]
  exact step _

/-- Two equal natural-indexed states along a bi-infinite path cut out a
directed cycle. -/
theorem hasCycle_of_path_repeat {α : Type*} {relation : α → α → Prop}
    {path : Int → α} (step : IsBiInfinitePath relation path)
    {first second : Nat} (less : first < second)
    (repeated : path first = path second) : HasCycle relation := by
  let distance := second - first
  have distancePositive : 0 < distance := by omega
  have distanceSize : (distance - 1) + 1 = distance := by omega
  refine ⟨distance - 1, fun index => path (first + index.val), ?_⟩
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
      have indexBound : index.val < distance := by omega
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

/-- A bi-infinite path through a finite state type repeats and hence contains
a directed cycle. -/
theorem hasCycle_of_hasBiInfinitePath {α : Type*} [Fintype α]
    {relation : α → α → Prop}
    (infinite : HasBiInfinitePath relation) : HasCycle relation := by
  obtain ⟨path, step⟩ := infinite
  let sample : Fin (Fintype.card α + 1) → α := fun index => path index.val
  obtain ⟨first, second, distinct, repeated⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt sample (by simp)
  have valueDistinct : first.val ≠ second.val := by
    intro equality
    exact distinct (Fin.ext equality)
  rcases Nat.lt_or_gt_of_ne valueDistinct with less | greater
  · exact hasCycle_of_path_repeat step less repeated
  · exact hasCycle_of_path_repeat step greater repeated.symm

/-- A finite transition relation admits a bi-infinite path exactly when it
contains a nonempty directed cycle. -/
theorem hasBiInfinitePath_iff_hasCycle {α : Type*} [Fintype α]
    (relation : α → α → Prop) :
    HasBiInfinitePath relation ↔ HasCycle relation :=
  ⟨hasCycle_of_hasBiInfinitePath, hasBiInfinitePath_of_hasCycle⟩

end LeanTrominoes.FiniteState

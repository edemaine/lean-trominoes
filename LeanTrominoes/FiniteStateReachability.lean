/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateSearch
import Mathlib.Data.Nat.Log

/-!
# Logarithmic-depth finite-state reachability

This file formalizes the Savitch recurrence used by the 1.5D PSPACE upper
bound.  It proves that recursion level `d` decides walks of length at most
`2 ^ d`, and that successor-logarithmic depth covers every state of a finite
transition graph.  The executable recurrence deterministically enumerates
midpoints while retaining only a logarithmic recursion stack.
-/

namespace LeanTrominoes.FiniteState

/-- A walk of exactly `length` directed edges. -/
inductive ReachIn {α : Type*} (relation : α → α → Prop) :
    Nat → α → α → Prop
  | refl (state : α) : ReachIn relation 0 state state
  | tail {length : Nat} {first middle last : α} :
      ReachIn relation length first middle →
      relation middle last →
      ReachIn relation (length + 1) first last

/-- A walk using at most `bound` directed edges. -/
def ReachWithin {α : Type*} (relation : α → α → Prop)
    (bound : Nat) (first last : α) : Prop :=
  ∃ length ≤ bound, ReachIn relation length first last

namespace ReachIn

theorem trans {α : Type*} {relation : α → α → Prop}
    {first middle last : α} {firstLength secondLength : Nat}
    (firstReach : ReachIn relation firstLength first middle)
    (secondReach : ReachIn relation secondLength middle last) :
    ReachIn relation (firstLength + secondLength) first last := by
  induction secondReach generalizing first firstLength with
  | refl =>
      simpa using firstReach
  | tail previous edge ih =>
      have combined := ih firstReach
      simpa [Nat.add_assoc] using ReachIn.tail combined edge

theorem split {α : Type*} {relation : α → α → Prop}
    {length prefixLength : Nat} {first last : α}
    (walk : ReachIn relation length first last)
    (prefixBound : prefixLength ≤ length) :
    ∃ middle,
      ReachIn relation prefixLength first middle ∧
        ReachIn relation (length - prefixLength) middle last := by
  induction walk generalizing prefixLength with
  | refl state =>
      have prefixZero : prefixLength = 0 := by omega
      subst prefixLength
      exact ⟨state, ReachIn.refl state, ReachIn.refl state⟩
  | @tail length first previous last walk edge ih =>
      by_cases all : prefixLength = length + 1
      · subst prefixLength
        refine ⟨last, ReachIn.tail walk edge, ?_⟩
        simp
        exact ReachIn.refl last
      · have prefixBefore : prefixLength ≤ length := by omega
        obtain ⟨middle, firstPart, secondPart⟩ :=
          ih prefixBefore
        refine ⟨middle, firstPart, ?_⟩
        have extended := ReachIn.tail secondPart edge
        convert extended using 1
        omega

end ReachIn

namespace ReachWithin

theorem refl {α : Type*} {relation : α → α → Prop}
    (bound : Nat) (state : α) :
    ReachWithin relation bound state state :=
  ⟨0, Nat.zero_le _, ReachIn.refl state⟩

theorem single {α : Type*} {relation : α → α → Prop}
    {bound : Nat} (boundPositive : 0 < bound)
    {first last : α} (edge : relation first last) :
    ReachWithin relation bound first last :=
  ⟨1, boundPositive, ReachIn.tail (ReachIn.refl first) edge⟩

theorem trans {α : Type*} {relation : α → α → Prop}
    {first middle last : α} {firstBound secondBound : Nat}
    (firstReach : ReachWithin relation firstBound first middle)
    (secondReach : ReachWithin relation secondBound middle last) :
    ReachWithin relation (firstBound + secondBound) first last := by
  obtain ⟨firstLength, firstLe, firstWalk⟩ := firstReach
  obtain ⟨secondLength, secondLe, secondWalk⟩ := secondReach
  exact ⟨firstLength + secondLength, Nat.add_le_add firstLe secondLe,
    firstWalk.trans secondWalk⟩

end ReachWithin

/-- Propositional Savitch recurrence. Level `depth` represents walks of
length at most `2 ^ depth`. -/
def DivideReach {α : Type*} (relation : α → α → Prop) :
    Nat → α → α → Prop
  | 0, first, last => first = last ∨ relation first last
  | depth + 1, first, last =>
      ∃ middle,
        DivideReach relation depth first middle ∧
          DivideReach relation depth middle last

theorem divideReach_iff_reachWithin_pow {α : Type*}
    (relation : α → α → Prop) (depth : Nat) (first last : α) :
    DivideReach relation depth first last ↔
      ReachWithin relation (2 ^ depth) first last := by
  induction depth generalizing first last with
  | zero =>
      constructor
      · rintro (rfl | edge)
        · exact ReachWithin.refl 1 first
        · exact ReachWithin.single (by omega) edge
      · rintro ⟨length, lengthBound, walk⟩
        simp only [pow_zero] at lengthBound
        rcases length with _ | length
        · left
          cases walk
          rfl
        · have lengthZero : length = 0 := by omega
          subst length
          right
          cases walk with
          | tail previous edge =>
              cases previous
              exact edge
  | succ depth ih =>
      constructor
      · rintro ⟨middle, firstHalf, secondHalf⟩
        have combined :=
          ReachWithin.trans
            ((ih first middle).mp firstHalf)
            ((ih middle last).mp secondHalf)
        simpa [pow_succ, Nat.mul_two] using combined
      · intro reach
        rw [pow_succ] at reach
        obtain ⟨length, lengthBound, walk⟩ := reach
        by_cases firstHalf : length ≤ 2 ^ depth
        · exact ⟨last, (ih first last).mpr
            ⟨length, firstHalf, walk⟩,
            (ih last last).mpr (ReachWithin.refl _ last)⟩
        · have halfBound : 2 ^ depth ≤ length := by omega
          obtain ⟨middle, prefixWalk, suffixWalk⟩ :=
            walk.split halfBound
          refine ⟨middle,
            (ih first middle).mpr
              ⟨2 ^ depth, le_rfl, prefixWalk⟩,
            (ih middle last).mpr
              ⟨length - 2 ^ depth, ?_, suffixWalk⟩⟩
          omega

/-- Executable Savitch recurrence over a finite state type. -/
def divideReachBool {α : Type*} [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation] :
    Nat → α → α → Bool
  | 0, first, last => decide (first = last ∨ relation first last)
  | depth + 1, first, last =>
      decide (∃ middle,
        divideReachBool relation depth first middle = true ∧
          divideReachBool relation depth middle last = true)

theorem divideReachBool_eq_true_iff {α : Type*}
    [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation]
    (depth : Nat) (first last : α) :
    divideReachBool relation depth first last = true ↔
      DivideReach relation depth first last := by
  induction depth generalizing first last with
  | zero =>
      simp [divideReachBool, DivideReach]
  | succ depth ih =>
      simp [divideReachBool, DivideReach, ih, decide_eq_true_eq]

/-- Logarithmic recursion depth sufficient to cover the entire finite state
space. -/
def savitchDepth (α : Type*) [Fintype α] : Nat :=
  (Nat.log 2 (Fintype.card α)).succ

theorem card_lt_pow_savitchDepth (α : Type*) [Fintype α] :
    Fintype.card α < 2 ^ savitchDepth α := by
  exact Nat.lt_pow_succ_log_self Nat.one_lt_two _

theorem card_le_pow_savitchDepth (α : Type*) [Fintype α] :
    Fintype.card α ≤ 2 ^ savitchDepth α :=
  (card_lt_pow_savitchDepth α).le

/-- At the canonical logarithmic depth, the executable recurrence decides
walks up to a bound covering every state of the finite graph. -/
theorem divideReachBool_savitchDepth_eq_true_iff {α : Type*}
    [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation]
    (first last : α) :
    divideReachBool relation (savitchDepth α) first last = true ↔
      ReachWithin relation (2 ^ savitchDepth α) first last := by
  rw [divideReachBool_eq_true_iff,
    divideReach_iff_reachWithin_pow]

end LeanTrominoes.FiniteState

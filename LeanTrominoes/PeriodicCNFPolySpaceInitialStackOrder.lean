/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineEmptyStackEmitter
import Mathlib.Data.List.TakeWhile

/-!
# Exact stack order around the input stack

The finite enumeration of machine stacks need not begin with `k₀`.  Split it
at the unique occurrence of `k₀`, preserving the exact enumeration order.
This lets the normalized initial-configuration emitter run ordinary empty-stack
passes before and after the type-changing input-stack pass without assuming a
special `Fintype` order.
-/

noncomputable section

namespace LeanTrominoes

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace PolySpaceInitialStackOrder

open BoundedMachineAtom

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

def beforeValue {Value : Type} [DecidableEq Value]
    (value : Value) (values : List Value) : List Value :=
  values.takeWhile fun candidate => decide (candidate ≠ value)

def afterValue {Value : Type} [DecidableEq Value]
    (value : Value) (values : List Value) : List Value :=
  (values.dropWhile fun candidate => decide (candidate ≠ value)).tail

/-- Splitting at a member gives the exact original order. -/
theorem values_eq_before_cons_after {Value : Type} [DecidableEq Value]
    (value : Value) (values : List Value) (membership : value ∈ values) :
    values = beforeValue value values ++ value :: afterValue value values := by
  induction values with
  | nil => simp at membership
  | cons head values induction =>
      by_cases equal : head = value
      · subst head
        simp only [beforeValue, afterValue]
        have rejected : ¬ decide (value ≠ value) := by simp
        rw [List.takeWhile_cons_of_neg
            (p := fun candidate => decide (candidate ≠ value)) rejected,
          List.dropWhile_cons_of_neg
            (p := fun candidate => decide (candidate ≠ value)) rejected]
        rfl
      · have tailMembership : value ∈ values := by
          have reverse : value ≠ head := Ne.symm equal
          simpa [reverse] using membership
        have rest := induction tailMembership
        simp only [beforeValue, afterValue] at rest ⊢
        have chosen : decide (head ≠ value) := by simp [equal]
        rw [List.takeWhile_cons_of_pos
            (p := fun candidate => decide (candidate ≠ value)) chosen,
          List.dropWhile_cons_of_pos
            (p := fun candidate => decide (candidate ≠ value)) chosen]
        simp only [List.cons_append, List.cons.injEq]
        exact ⟨True.intro, rest⟩

def beforeInput : List decider.tm.K :=
  beforeValue decider.tm.k₀ (finiteValues decider.tm.K)

def afterInput : List decider.tm.K :=
  afterValue decider.tm.k₀ (finiteValues decider.tm.K)

/-- Exact decomposition of the fixed finite stack enumeration. -/
theorem finiteValues_eq_before_input_after :
    finiteValues decider.tm.K =
      beforeInput decider ++ decider.tm.k₀ :: afterInput decider := by
  exact values_eq_before_cons_after decider.tm.k₀
    (finiteValues decider.tm.K)
    (BoundedMachineAtom.mem_finiteValues decider.tm.k₀)

theorem beforeInput_ne (stack : decider.tm.K)
    (membership : stack ∈ beforeInput decider) :
    stack ≠ decider.tm.k₀ := by
  unfold beforeInput beforeValue at membership
  have selected := List.mem_takeWhile_imp membership
  simpa using selected

theorem input_not_mem_afterInput :
    decider.tm.k₀ ∉ afterInput decider := by
  have enumerationNodup :
      (beforeInput decider ++ decider.tm.k₀ :: afterInput decider).Nodup := by
    rw [← finiteValues_eq_before_input_after]
    exact BoundedMachineAtom.finiteValues_nodup decider.tm.K
  have suffixNodup :
      (decider.tm.k₀ :: afterInput decider).Nodup :=
    (List.nodup_append.mp enumerationNodup).2.1
  exact (List.nodup_cons.mp suffixNodup).1

theorem afterInput_ne (stack : decider.tm.K)
    (membership : stack ∈ afterInput decider) :
    stack ≠ decider.tm.k₀ := by
  intro equal
  subst stack
  exact input_not_mem_afterInput decider membership

/-- Any stack-indexed concatenation splits at the input stack in exactly the
same order as `finiteValues`. -/
theorem flatMap_finiteValues {Target : Type}
    (words : decider.tm.K → List Target) :
    (finiteValues decider.tm.K).flatMap words =
      (beforeInput decider).flatMap words ++
        words decider.tm.k₀ ++
        (afterInput decider).flatMap words := by
  rw [finiteValues_eq_before_input_after]
  simp [List.append_assoc]

@[simp]
theorem length_before_input_after :
    (beforeInput decider).length + 1 + (afterInput decider).length =
      Fintype.card decider.tm.K := by
  have lengths := congrArg List.length
    (finiteValues_eq_before_input_after decider)
  rw [BoundedMachineAtom.finiteValues_length] at lengths
  simp only [List.length_append, List.length_cons] at lengths
  omega

end PolySpaceInitialStackOrder
end PeriodicCNF
end LeanTrominoes

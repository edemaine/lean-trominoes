/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineWellFormed

/-!
# Decoding well-formed machine slices

This file closes the finite-field representation loop.  An exact-one Boolean
field has a unique selected value; applying that fact to every field decodes
an arbitrary valuation into a bounded machine slice.  The decoded slice is
proved to reproduce every label, state, stack-cell, and clock source bit.
The stack suffix constraints additionally make its fixed-width stack vectors
list-shaped.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace TransitionExpr

/-- A finite Boolean field has one selected value and no other true value. -/
def HasUniqueTrue {Value : Type*} (values : List Value)
    (bit : Value → Bool) : Prop :=
  ∃ selected ∈ values, bit selected = true ∧
    ∀ other ∈ values, bit other = true → other = selected

/-- The recursive exact-one predicate yields a uniquely selected source
value, even without assuming that the source list is duplicate-free. -/
theorem hasUniqueTrue_of_exactlyOne {Value : Type*}
    {values : List Value} {bit : Value → Bool}
    (exactlyOne : ExactlyOneTrue (values.map bit)) :
    HasUniqueTrue values bit := by
  induction values with
  | nil => exact exactlyOne.elim
  | cons head tail ih =>
      change (bit head = true ∧
          ∀ other ∈ tail.map bit, other = false) ∨
        (bit head = false ∧ ExactlyOneTrue (tail.map bit)) at exactlyOne
      rcases exactlyOne with headSelected | tailSelected
      · refine ⟨head, by simp, headSelected.1, ?_⟩
        intro other otherMem otherTrue
        rcases List.mem_cons.mp otherMem with rfl | otherTail
        · rfl
        · have bitMem : bit other ∈ tail.map bit :=
            List.mem_map.mpr ⟨other, otherTail, rfl⟩
          have falseValue := headSelected.2 (bit other) bitMem
          rw [otherTrue] at falseValue
          contradiction
      · obtain ⟨selected, selectedMem, selectedTrue, unique⟩ :=
          ih tailSelected.2
        refine ⟨selected, by simp [selectedMem], selectedTrue, ?_⟩
        intro other otherMem otherTrue
        rcases List.mem_cons.mp otherMem with rfl | otherTail
        · rw [tailSelected.1] at otherTrue
          contradiction
        · exact unique other otherTail otherTrue

/-- Select the unique true finite-field value, with a default used only on
malformed fields. -/
noncomputable def select {Value : Type*} (default : Value) (values : List Value)
    (bit : Value → Bool) : Value := by
  classical
  exact if unique : HasUniqueTrue values bit then unique.choose else default

theorem select_true {Value : Type*} {default : Value} {values : List Value}
    {bit : Value → Bool} (unique : HasUniqueTrue values bit) :
    bit (select default values bit) = true := by
  rw [select, dif_pos unique]
  exact unique.choose_spec.2.1

theorem eq_select_of_true {Value : Type*}
    {default : Value} {values : List Value}
    {bit : Value → Bool} (unique : HasUniqueTrue values bit)
    {candidate : Value} (candidateMem : candidate ∈ values)
    (candidateTrue : bit candidate = true) :
    candidate = select default values bit := by
  rw [select, dif_pos unique]
  exact unique.choose_spec.2.2 candidate candidateMem candidateTrue

theorem bit_eq_decide_select_eq {Value : Type*} [DecidableEq Value]
    {default : Value} {values : List Value} {bit : Value → Bool}
    (unique : HasUniqueTrue values bit) (candidate : Value)
    (candidateMem : candidate ∈ values) :
    bit candidate = decide (select default values bit = candidate) := by
  by_cases candidateTrue : bit candidate = true
  · have equality := eq_select_of_true (default := default)
      unique candidateMem candidateTrue
    have selectedTrue : bit (select default values bit) = true :=
      select_true unique
    simp [candidateTrue, equality, selectedTrue]
  · have selectedTrue := select_true (default := default) unique
    have unequal : select default values bit ≠ candidate := by
      intro equality
      apply candidateTrue
      rw [← equality]
      exact selectedTrue
    have candidateFalse : bit candidate = false :=
      Bool.eq_false_of_not_eq_true candidateTrue
    simp [candidateFalse, unequal]

end TransitionExpr

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

noncomputable local instance : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (stack : tm.K) : DecidableEq (tm.Γ stack) :=
  Classical.decEq _

/-- A decoded fixed-width machine slice.  Stack shape is kept as a separate
predicate so decoding remains total on malformed valuations. -/
structure BoundedMachineSlice (tm : FinTM2) (space clockBits : Nat) where
  label : Option tm.Λ
  control : tm.σ
  stack : ∀ stack : tm.K, Fin space → Option (tm.Γ stack)
  clock : Fin clockBits → Bool

/-- Every fixed-width stack vector is an occupied prefix followed by `none`. -/
def BoundedMachineSlice.StackShaped
    (slice : BoundedMachineSlice tm space clockBits) : Prop :=
  ∀ (stack : tm.K) (index : Nat) (nextExists : index + 1 < space),
    slice.stack stack ⟨index, Nat.lt_of_succ_lt nextExists⟩ = none →
      slice.stack stack ⟨index + 1, nextExists⟩ = none

/-- Decode every finite field by its selected source atom and copy clock bits
directly. -/
def decode (valuation : Nat → Bool) :
    BoundedMachineSlice tm space clockBits where
  label := TransitionExpr.select none (finiteValues (Option tm.Λ))
    fun labelValue => valuation
      (code (.label labelValue : BoundedMachineAtom tm space clockBits))
  control := TransitionExpr.select tm.initialState (finiteValues tm.σ)
    fun control => valuation
      (code (.state control : BoundedMachineAtom tm space clockBits))
  stack stack position :=
    TransitionExpr.select none (finiteValues (Option (tm.Γ stack)))
      fun symbol => valuation
        (code (.stack ⟨stack, position, symbol⟩ :
          BoundedMachineAtom tm space clockBits))
  clock position := valuation
    (code (.clock position : BoundedMachineAtom tm space clockBits))

private theorem field_true_of_oneHot
    {valuation : Nat → Bool} {expression : TransitionExpr}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (member : expression ∈ oneHotFieldExpressions
      (tm := tm) (space := space) (clockBits := clockBits)) :
    expression.eval valuation valuation = true := by
  have allTrue :
      (oneHotFieldExpressions (tm := tm) (space := space)
        (clockBits := clockBits)).all
          (fun field => field.eval valuation valuation) = true := by
    simpa [oneHotFields] using oneHot
  exact (List.all_eq_true.mp allTrue) expression member

theorem label_exactlyOne_of_oneHot {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    TransitionExpr.ExactlyOneTrue
      ((finiteValues (Option tm.Λ)).map fun labelValue => valuation
        (code (.label labelValue :
          BoundedMachineAtom tm space clockBits))) := by
  have fieldTrue := field_true_of_oneHot oneHot (expression :=
    TransitionExpr.currentExactlyOne
      (labelAtoms (tm := tm) (space := space) (clockBits := clockBits)))
    (by simp [oneHotFieldExpressions])
  have atomExact := (TransitionExpr.currentExactlyOne_eval_iff
    (labelAtoms (tm := tm) (space := space) (clockBits := clockBits))
    valuation valuation).mp fieldTrue
  simpa [labelAtoms, List.map_map, Function.comp_def] using atomExact

theorem state_exactlyOne_of_oneHot {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    TransitionExpr.ExactlyOneTrue
      ((finiteValues tm.σ).map fun control => valuation
        (code (.state control :
          BoundedMachineAtom tm space clockBits))) := by
  have fieldTrue := field_true_of_oneHot oneHot (expression :=
    TransitionExpr.currentExactlyOne
      (stateAtoms (tm := tm) (space := space) (clockBits := clockBits)))
    (by simp [oneHotFieldExpressions])
  have atomExact := (TransitionExpr.currentExactlyOne_eval_iff
    (stateAtoms (tm := tm) (space := space) (clockBits := clockBits))
    valuation valuation).mp fieldTrue
  simpa [stateAtoms, List.map_map, Function.comp_def] using atomExact

theorem stack_exactlyOne_of_oneHot {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (stack : tm.K) (position : Fin space) :
    TransitionExpr.ExactlyOneTrue
      ((finiteValues (Option (tm.Γ stack))).map fun symbol => valuation
        (code (.stack ⟨stack, position, symbol⟩ :
          BoundedMachineAtom tm space clockBits))) := by
  have fieldMem : TransitionExpr.currentExactlyOne
      (stackCellAtoms (tm := tm) (clockBits := clockBits) stack position) ∈
      oneHotFieldExpressions (tm := tm) (space := space)
        (clockBits := clockBits) := by
    rw [oneHotFieldExpressions, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨stack, mem_finiteValues stack, ?_⟩
    apply List.mem_map.mpr
    exact ⟨position, by simp, rfl⟩
  have fieldTrue := field_true_of_oneHot oneHot fieldMem
  have atomExact := (TransitionExpr.currentExactlyOne_eval_iff
    (stackCellAtoms (tm := tm) (clockBits := clockBits) stack position)
    valuation valuation).mp fieldTrue
  simpa [stackCellAtoms, List.map_map, Function.comp_def] using atomExact

theorem decode_label_bit {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (labelValue : Option tm.Λ) :
    valuation (code (.label labelValue :
        BoundedMachineAtom tm space clockBits)) =
      decide ((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).label = labelValue) := by
  have unique := TransitionExpr.hasUniqueTrue_of_exactlyOne
    (label_exactlyOne_of_oneHot oneHot)
  let selected := TransitionExpr.select none (finiteValues (Option tm.Λ))
    fun candidate => valuation
      (code (.label candidate : BoundedMachineAtom tm space clockBits))
  by_cases equality : selected = labelValue
  · have selectedTrue := TransitionExpr.select_true (default := none) unique
    change valuation (code (.label selected :
      BoundedMachineAtom tm space clockBits)) = true at selectedTrue
    subst labelValue
    simpa [decode, selected] using selectedTrue
  · have candidateFalse : valuation (code (.label labelValue :
        BoundedMachineAtom tm space clockBits)) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro candidateTrue
      have candidateEq := TransitionExpr.eq_select_of_true
        (default := none) unique (mem_finiteValues labelValue) candidateTrue
      exact equality candidateEq.symm
    simpa [decode, selected, equality, candidateFalse]

theorem decode_state_bit {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (control : tm.σ) :
    valuation (code (.state control :
        BoundedMachineAtom tm space clockBits)) =
      decide ((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).control = control) := by
  have unique := TransitionExpr.hasUniqueTrue_of_exactlyOne
    (state_exactlyOne_of_oneHot oneHot)
  let selected := TransitionExpr.select tm.initialState (finiteValues tm.σ)
    fun candidate => valuation
      (code (.state candidate : BoundedMachineAtom tm space clockBits))
  by_cases equality : selected = control
  · have selectedTrue := TransitionExpr.select_true
      (default := tm.initialState) unique
    change valuation (code (.state selected :
      BoundedMachineAtom tm space clockBits)) = true at selectedTrue
    subst control
    simpa [decode, selected] using selectedTrue
  · have candidateFalse : valuation (code (.state control :
        BoundedMachineAtom tm space clockBits)) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro candidateTrue
      have candidateEq := TransitionExpr.eq_select_of_true
        (default := tm.initialState) unique (mem_finiteValues control)
          candidateTrue
      exact equality candidateEq.symm
    simpa [decode, selected, equality, candidateFalse]

theorem decode_stack_bit {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (stack : tm.K) (position : Fin space) (symbol : Option (tm.Γ stack)) :
    valuation (code (.stack ⟨stack, position, symbol⟩ :
        BoundedMachineAtom tm space clockBits)) =
      decide ((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).stack stack position = symbol) := by
  have unique := TransitionExpr.hasUniqueTrue_of_exactlyOne
    (stack_exactlyOne_of_oneHot oneHot stack position)
  let selected := TransitionExpr.select none
    (finiteValues (Option (tm.Γ stack))) fun candidate => valuation
      (code (.stack ⟨stack, position, candidate⟩ :
        BoundedMachineAtom tm space clockBits))
  by_cases equality : selected = symbol
  · have selectedTrue := TransitionExpr.select_true (default := none) unique
    change valuation (code (.stack ⟨stack, position, selected⟩ :
      BoundedMachineAtom tm space clockBits)) = true at selectedTrue
    subst symbol
    simpa [decode, selected] using selectedTrue
  · have candidateFalse : valuation (code (.stack ⟨stack, position, symbol⟩ :
        BoundedMachineAtom tm space clockBits)) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro candidateTrue
      have candidateEq := TransitionExpr.eq_select_of_true
        (default := none) unique (mem_finiteValues symbol) candidateTrue
      exact equality candidateEq.symm
    simpa [decode, selected, equality, candidateFalse]

@[simp]
theorem decode_clock_bit (valuation : Nat → Bool)
    (position : Fin clockBits) :
    (decode (tm := tm) (space := space)
      (clockBits := clockBits) valuation).clock position =
        valuation (code (.clock position :
          BoundedMachineAtom tm space clockBits)) :=
  rfl

private theorem suffix_field_true
    {valuation : Nat → Bool}
    (suffix : (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (stack : tm.K) (index : Nat) (indexLt : index < space) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).eval valuation valuation = true := by
  have allTrue :
      (allStackSuffixExpressions (tm := tm) (space := space)
        (clockBits := clockBits)).all
          (fun field => field.eval valuation valuation) = true := by
    simpa [stackSuffixFields] using suffix
  apply (List.all_eq_true.mp allTrue)
  rw [allStackSuffixExpressions, List.mem_flatMap]
  refine ⟨stack, mem_finiteValues stack, ?_⟩
  rw [stackSuffixExpressions]
  apply List.mem_map.mpr
  exact ⟨index, by simp [indexLt], rfl⟩

theorem decode_stackShaped {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (suffix : (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    (decode (tm := tm) (space := space)
      (clockBits := clockBits) valuation).StackShaped := by
  intro stack index nextExists currentNone
  have fieldTrue := suffix_field_true suffix stack index
    (Nat.lt_of_succ_lt nextExists)
  have currentBit := decode_stack_bit oneHot stack
    ⟨index, Nat.lt_of_succ_lt nextExists⟩ none
  have nextBit := decode_stack_bit oneHot stack
    ⟨index + 1, nextExists⟩ none
  rw [stackSuffixExpression, dif_pos nextExists] at fieldTrue
  simp only [TransitionExpr.eval, TransitionExpr.current_eval,
    stackNoneAtom] at fieldTrue
  rw [currentBit, nextBit] at fieldTrue
  simpa [currentNone] using fieldTrue

/-- Every structurally well-formed valuation decodes to a list-shaped bounded
slice and is reproduced exactly on every source atom. -/
theorem decode_of_wellFormed {valuation : Nat → Bool}
    (wellFormed : (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    let slice := decode (tm := tm) (space := space)
      (clockBits := clockBits) valuation
    slice.StackShaped ∧
      (∀ labelValue, valuation (code (.label labelValue :
        BoundedMachineAtom tm space clockBits)) =
          decide (slice.label = labelValue)) ∧
      (∀ control, valuation (code (.state control :
        BoundedMachineAtom tm space clockBits)) =
          decide (slice.control = control)) ∧
      (∀ stack position symbol,
        valuation (code (.stack ⟨stack, position, symbol⟩ :
          BoundedMachineAtom tm space clockBits)) =
            decide (slice.stack stack position = symbol)) ∧
      (∀ position, slice.clock position = valuation
        (code (.clock position :
          BoundedMachineAtom tm space clockBits))) := by
  have parts :
      (oneHotFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval valuation valuation = true ∧
      (stackSuffixFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval valuation valuation = true := by
    simpa [wellFormedFields, TransitionExpr.eval] using wellFormed
  exact ⟨decode_stackShaped parts.1 parts.2,
    fun labelValue => decode_label_bit parts.1 labelValue,
    fun control => decode_state_bit parts.1 control,
    fun stack position symbol => decode_stack_bit parts.1 stack position symbol,
    fun position => decode_clock_bit valuation position⟩

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Restricting supported TM2 programs to finite machines

Mathlib's stack-machine developments often describe programs using an
infinite ambient label type and then prove that only a particular finite
`Finset` of labels is reachable.  `FinTM2`, used by the complexity interface,
instead requires a genuinely finite label type.  This file performs that
restriction and proves that erasing label-membership proofs commutes with one
machine step.
-/

namespace Turing
namespace TM2

open Relation

/-- Replace every jump target in a supported statement by the corresponding
element of the finite label subtype. -/
def restrictStmt {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    (labels : Finset Λ) :
    (statement : Stmt Γ Λ σ) →
      SupportsStmt labels statement →
        Stmt Γ { label // label ∈ labels } σ
  | .push stack write next, supported =>
      .push stack write (restrictStmt labels next supported)
  | .peek stack read next, supported =>
      .peek stack read (restrictStmt labels next supported)
  | .pop stack read next, supported =>
      .pop stack read (restrictStmt labels next supported)
  | .load update next, supported =>
      .load update (restrictStmt labels next supported)
  | .branch test yes no, supported =>
      .branch test
        (restrictStmt labels yes supported.1)
        (restrictStmt labels no supported.2)
  | .goto target, supported =>
      .goto fun state => ⟨target state, supported state⟩
  | .halt, _ => .halt

/-- Restrict a supported program to its finite label subtype. -/
def restrictProgram {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] (program : Λ → Stmt Γ Λ σ) (labels : Finset Λ)
    (supported : Supports program labels) :
    { label // label ∈ labels } →
      Stmt Γ { label // label ∈ labels } σ :=
  fun label =>
    restrictStmt labels (program label.1)
      (supported.2 label.1 label.2)

/-- Erase finite-support membership proofs from a restricted configuration. -/
def eraseRestrictedCfg {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {labels : Finset Λ}
    (configuration : Cfg Γ { label // label ∈ labels } σ) :
    Cfg Γ Λ σ where
  l := configuration.l.map Subtype.val
  var := configuration.var
  stk := configuration.stk

theorem eraseRestrictedCfg_restrictStmt_stepAux
    {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (labels : Finset Λ) (statement : Stmt Γ Λ σ)
    (supported : SupportsStmt labels statement)
    (state : σ) (stackContents : ∀ stack : K, List (Γ stack)) :
    eraseRestrictedCfg
        (stepAux (restrictStmt labels statement supported)
          state stackContents) =
      stepAux statement state stackContents := by
  induction statement generalizing state stackContents with
  | push stack write next ih =>
      simpa only [restrictStmt, stepAux] using
        ih supported state
          (Function.update stackContents stack
            (write state :: stackContents stack))
  | peek stack read next ih =>
      simpa only [restrictStmt, stepAux] using
        ih supported (read state (stackContents stack).head?) stackContents
  | pop stack read next ih =>
      simpa only [restrictStmt, stepAux] using
        ih supported (read state (stackContents stack).head?)
          (Function.update stackContents stack (stackContents stack).tail)
  | load update next ih =>
      simpa only [restrictStmt, stepAux] using
        ih supported (update state) stackContents
  | branch test yes no yesIH noIH =>
      cases tested : test state with
      | false =>
          simpa [restrictStmt, stepAux, tested] using
            noIH supported.2 state stackContents
      | true =>
          simpa [restrictStmt, stepAux, tested] using
            yesIH supported.1 state stackContents
  | goto target =>
      rfl
  | halt =>
      rfl

theorem eraseRestrictedCfg_restrictProgram_step
    {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] (program : Λ → Stmt Γ Λ σ) (labels : Finset Λ)
    (supported : Supports program labels)
    (configuration : Cfg Γ { label // label ∈ labels } σ) :
    Option.map eraseRestrictedCfg
        (step (restrictProgram program labels supported) configuration) =
      step program (eraseRestrictedCfg configuration) := by
  cases configuration with
  | mk label state stackContents =>
      cases label with
      | none => rfl
      | some label =>
          simp only [step, restrictProgram, Option.map_some]
          exact congrArg some
            (eraseRestrictedCfg_restrictStmt_stepAux labels
              (program label.1) (supported.2 label.1 label.2)
              state stackContents)

/-- Attach finite-support membership proofs to every live label of an ambient
configuration known to stay within the support. -/
def restrictCfg {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    (labels : Finset Λ) (configuration : Cfg Γ Λ σ)
    (within : configuration.l ∈ Finset.insertNone labels) :
    Cfg Γ { label // label ∈ labels } σ where
  l :=
    match labelEq : configuration.l with
    | none => none
    | some label =>
        some ⟨label, by
          apply Finset.some_mem_insertNone.mp
          rw [← labelEq]
          exact within⟩
  var := configuration.var
  stk := configuration.stk

@[simp]
theorem eraseRestrictedCfg_restrictCfg
    {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    (labels : Finset Λ) (configuration : Cfg Γ Λ σ)
    (within : configuration.l ∈ Finset.insertNone labels) :
    eraseRestrictedCfg (restrictCfg labels configuration within) =
      configuration := by
  cases configuration with
  | mk label state stackContents =>
      cases label <;> rfl

theorem eraseRestrictedCfg_label_mem
    {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {labels : Finset Λ}
    (configuration : Cfg Γ { label // label ∈ labels } σ) :
    (eraseRestrictedCfg configuration).l ∈
      Finset.insertNone labels := by
  cases configuration with
  | mk label state stackContents =>
      cases label with
      | none =>
          exact Finset.none_mem_insertNone
      | some label =>
          exact Finset.some_mem_insertNone.mpr label.2

@[simp]
theorem restrictCfg_eraseRestrictedCfg
    {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {labels : Finset Λ}
    (configuration : Cfg Γ { label // label ∈ labels } σ) :
    restrictCfg labels (eraseRestrictedCfg configuration)
        (eraseRestrictedCfg_label_mem configuration) =
      configuration := by
  cases configuration with
  | mk label state stackContents =>
      cases label <;> rfl

theorem eraseRestrictedCfg_injective
    {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {labels : Finset Λ} :
    Function.Injective
      (eraseRestrictedCfg :
        Cfg Γ { label // label ∈ labels } σ → Cfg Γ Λ σ) := by
  rintro ⟨firstLabel, firstState, firstStacks⟩
    ⟨secondLabel, secondState, secondStacks⟩ equality
  cases firstLabel with
  | none =>
      cases secondLabel with
      | none =>
          simp [eraseRestrictedCfg] at equality
          rcases equality with ⟨stateEq, stacksEq⟩
          subst secondState
          subst secondStacks
          rfl
      | some secondLabel =>
          simp [eraseRestrictedCfg] at equality
  | some firstLabel =>
      cases secondLabel with
      | none =>
          simp [eraseRestrictedCfg] at equality
      | some secondLabel =>
          simp [eraseRestrictedCfg] at equality
          rcases equality with ⟨labelEq, stateEq, stacksEq⟩
          subst secondLabel
          subst secondState
          subst secondStacks
          rfl

/-- Every supported ambient step lifts uniquely to the finite restricted
program. -/
theorem restrictCfg_step
    {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] (program : Λ → Stmt Γ Λ σ) (labels : Finset Λ)
    (supported : Supports program labels)
    {before after : Cfg Γ Λ σ}
    (beforeWithin : before.l ∈ Finset.insertNone labels)
    (stepTo : after ∈ step program before) :
    let afterWithin :=
      step_supports program supported stepTo beforeWithin
    restrictCfg labels after afterWithin ∈
      step (restrictProgram program labels supported)
        (restrictCfg labels before beforeWithin) := by
  let afterWithin :=
    step_supports program supported stepTo beforeWithin
  have erasedStep :=
    eraseRestrictedCfg_restrictProgram_step program labels supported
      (restrictCfg labels before beforeWithin)
  rw [eraseRestrictedCfg_restrictCfg] at erasedStep
  simp only [Option.mem_def] at stepTo ⊢
  rw [stepTo] at erasedStep
  cases restrictedStep :
      step (restrictProgram program labels supported)
        (restrictCfg labels before beforeWithin) with
  | none =>
      simp [restrictedStep] at erasedStep
  | some result =>
      rw [restrictedStep] at erasedStep
      simp only [Option.map_some, Option.some.injEq] at erasedStep
      congr 1
      apply eraseRestrictedCfg_injective
      rw [erasedStep, eraseRestrictedCfg_restrictCfg]

/-- Every supported ambient execution lifts to the finite restricted
program. -/
theorem restrictCfg_reaches
    {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] (program : Λ → Stmt Γ Λ σ) (labels : Finset Λ)
    (supported : Supports program labels)
    {first last : Cfg Γ Λ σ}
    (firstWithin : first.l ∈ Finset.insertNone labels)
    (reaches : ReflTransGen
      (fun before after => after ∈ step program before) first last) :
    ∃ lastWithin : last.l ∈ Finset.insertNone labels,
      ReflTransGen
        (fun before after =>
          after ∈ step (restrictProgram program labels supported) before)
        (restrictCfg labels first firstWithin)
        (restrictCfg labels last lastWithin) := by
  induction reaches with
  | refl =>
      exact ⟨firstWithin, ReflTransGen.refl⟩
  | tail reaches stepTo ih =>
      obtain ⟨middleWithin, restrictedReaches⟩ := ih
      let lastWithin :=
        step_supports program supported stepTo middleWithin
      exact ⟨lastWithin, restrictedReaches.tail
        (restrictCfg_step program labels supported middleWithin stepTo)⟩

/-- Erasure maps every finite restricted execution to an execution of the
ambient program. -/
theorem eraseRestrictedCfg_reaches
    {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] (program : Λ → Stmt Γ Λ σ) (labels : Finset Λ)
    (supported : Supports program labels)
    {first last : Cfg Γ { label // label ∈ labels } σ}
    (reaches : ReflTransGen
      (fun before after =>
        after ∈ step (restrictProgram program labels supported) before)
      first last) :
    ReflTransGen (fun before after => after ∈ step program before)
      (eraseRestrictedCfg first) (eraseRestrictedCfg last) := by
  induction reaches with
  | refl =>
      exact ReflTransGen.refl
  | tail reaches edge ih =>
      apply ReflTransGen.tail ih
      simp only [Option.mem_def] at edge ⊢
      calc
        step program (eraseRestrictedCfg _) =
            Option.map eraseRestrictedCfg
              (step (restrictProgram program labels supported) _) :=
          (eraseRestrictedCfg_restrictProgram_step
            program labels supported _).symm
        _ = some (eraseRestrictedCfg _) := by
          rw [edge]
          simp

/-- Total cells stored across the stacks of an unbundled TM2
configuration. -/
def stackSpace {K : Type*} [Fintype K] {Γ : K → Type*} {Λ σ : Type*}
    (configuration : Cfg Γ Λ σ) : Nat :=
  ∑ stack, (configuration.stk stack).length

/-- Restricting labels changes no stack contents or space usage. -/
theorem stackSpace_eraseRestrictedCfg
    {K : Type*} [Fintype K] {Γ : K → Type*} {Λ σ : Type*}
    {labels : Finset Λ}
    (configuration : Cfg Γ { label // label ∈ labels } σ) :
    stackSpace (eraseRestrictedCfg configuration) =
      stackSpace configuration :=
  rfl

end TM2

/-- A reflexive-transitive execution admits Mathlib's step-counted `EvalsTo`
certificate. -/
theorem nonempty_evalsTo_of_reaches {state : Type*}
    {transition : state → Option state} {first last : state}
    (reaches : StateTransition.Reaches transition first last) :
    Nonempty (StateTransition.EvalsTo transition first (some last)) := by
  induction reaches with
  | refl =>
      exact ⟨StateTransition.EvalsTo.refl transition first⟩
  | @tail middle last reaches stepTo ih =>
      obtain ⟨ih⟩ := ih
      refine ⟨StateTransition.EvalsTo.trans transition first middle
        (some last) ih ⟨1, ?_⟩⟩
      simp only [Option.mem_def] at stepTo
      simp only [Function.iterate_one]
      change transition middle = some last
      exact stepTo

/-- Noncomputably select the step count forgotten by `Reaches`. -/
noncomputable def EvalsTo.of_reaches {state : Type*}
    {transition : state → Option state} {first last : state}
    (reaches : StateTransition.Reaches transition first last) :
    StateTransition.EvalsTo transition first (some last) :=
  Classical.choice (nonempty_evalsTo_of_reaches reaches)

/-- Bundle a supported ambient TM2 program as a machine with an actually
finite label type. -/
def FinTM2.ofSupported
    {K : Type} [DecidableEq K] [Fintype K]
    (inputStack outputStack : K)
    (Γ : K → Type) [Fintype (Γ inputStack)]
    {Λ σ : Type} [Inhabited Λ] [Fintype σ]
    (initialState : σ)
    (program : Λ → TM2.Stmt Γ Λ σ)
    (labels : Finset Λ) (supported : TM2.Supports program labels) :
    FinTM2 where
  K := K
  k₀ := inputStack
  k₁ := outputStack
  Γ := Γ
  Λ := { label // label ∈ labels }
  main := ⟨default, supported.1⟩
  σ := σ
  initialState := initialState
  m := TM2.restrictProgram program labels supported

end Turing

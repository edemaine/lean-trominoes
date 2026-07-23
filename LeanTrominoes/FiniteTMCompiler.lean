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

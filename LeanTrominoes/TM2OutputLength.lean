import LeanTrominoes.Complexity
import LeanTrominoes.FiniteTMCompiler

/-!
# Polynomial output-length bounds for polynomial-time TM2 machines

Mathlib's `TM2ComputableInPolyTime` counts one whole finite statement as one
machine step.  A statement can contain several primitive pushes, but a fixed
finite machine has a uniform constant bound on how many.  Consequently its
total stack population, and in particular its output length, grows at most
linearly with its counted running time.

This quantitative fact is needed to compose polynomial-time machines: the
second machine's polynomial must be evaluated at the intermediate encoding
length, which this file bounds by an explicit polynomial in the original
input length.
-/

noncomputable section

namespace LeanTrominoes

open scoped BigOperators

open StateTransition Turing

namespace TM2OutputLength

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Maximum number of primitive pushes performed along one control-flow path
through a single `TM2` statement. -/
def statementPushCount {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushCount next + 1
  | .peek _ _ next => statementPushCount next
  | .pop _ _ next => statementPushCount next
  | .load _ next => statementPushCount next
  | .branch _ yes no => max (statementPushCount yes) (statementPushCount no)
  | .goto _ => 0
  | .halt => 0

private theorem stackSpace_update_le
    {K : Type*} [DecidableEq K] [Fintype K]
    {Γ : K → Type*} {Λ σ : Type*}
    (label : Option Λ) (state : σ)
    (stackContents : ∀ stack, List (Γ stack))
    (target : K) (value : List (Γ target)) (extra : Nat)
    (lengthBound : value.length ≤
      (stackContents target).length + extra) :
    TM2.stackSpace
        ⟨label, state, Function.update stackContents target value⟩ ≤
      TM2.stackSpace ⟨label, state, stackContents⟩ + extra := by
  classical
  unfold TM2.stackSpace
  calc
    (∑ stack, (Function.update stackContents target value stack).length) ≤
        ∑ stack, ((stackContents stack).length +
          if stack = target then extra else 0) := by
      apply Finset.sum_le_sum
      intro stack member
      by_cases equal : stack = target
      · subst stack
        simpa using lengthBound
      · simp [Function.update_of_ne equal]
    _ = (∑ stack, (stackContents stack).length) + extra := by
      rw [Finset.sum_add_distrib]
      simp

private theorem stackSpace_update_tail_le
    {K : Type*} [DecidableEq K] [Fintype K]
    {Γ : K → Type*} {Λ σ : Type*}
    (label : Option Λ) (state : σ)
    (stackContents : ∀ stack, List (Γ stack)) (target : K) :
    TM2.stackSpace
        ⟨label, state,
          Function.update stackContents target
            (stackContents target).tail⟩ ≤
      TM2.stackSpace ⟨label, state, stackContents⟩ := by
  simpa using stackSpace_update_le label state stackContents target
    (stackContents target).tail 0 (by simp)

/-- Executing one finite statement increases total stack population by at
most its syntactic push count. -/
theorem stepAux_stackSpace_le
    {K : Type*} [DecidableEq K] [Fintype K]
    {Γ : K → Type*} {Λ σ : Type*}
    (statement : TM2.Stmt Γ Λ σ) (state : σ)
    (stackContents : ∀ stack, List (Γ stack)) :
    TM2.stackSpace (TM2.stepAux statement state stackContents) ≤
      TM2.stackSpace ⟨(none : Option Λ), state, stackContents⟩ +
        statementPushCount statement := by
  induction statement generalizing state stackContents with
  | push stack write next induction =>
      have recursive := induction state
        (Function.update stackContents stack
          (write state :: stackContents stack))
      have pushed := stackSpace_update_le (Λ := Λ) none state
        stackContents stack (write state :: stackContents stack) 1 (by simp)
      calc
        TM2.stackSpace
            (TM2.stepAux next state
              (Function.update stackContents stack
                (write state :: stackContents stack))) ≤
          TM2.stackSpace
              ⟨(none : Option Λ), state,
                Function.update stackContents stack
                  (write state :: stackContents stack)⟩ +
            statementPushCount next := recursive
        _ ≤ (TM2.stackSpace
              ⟨(none : Option Λ), state, stackContents⟩ + 1) +
            statementPushCount next :=
          Nat.add_le_add_right pushed _
        _ = TM2.stackSpace
              ⟨(none : Option Λ), state, stackContents⟩ +
            statementPushCount (.push stack write next) := by
          simp [statementPushCount]
          omega
  | peek stack read next induction =>
      simpa [statementPushCount, TM2.stackSpace] using
        induction (read state (stackContents stack).head?) stackContents
  | pop stack read next induction =>
      let nextState := read state (stackContents stack).head?
      let nextStacks := Function.update stackContents stack
        (stackContents stack).tail
      have recursive := induction nextState nextStacks
      have popped := stackSpace_update_tail_le (Λ := Λ) none nextState
        stackContents stack
      exact recursive.trans (by
        simp only [statementPushCount]
        exact Nat.add_le_add_right popped _)
  | load update next induction =>
      simpa [statementPushCount, TM2.stackSpace] using
        induction (update state) stackContents
  | branch test yes no yesInduction noInduction =>
      cases tested : test state with
      | false =>
          have recursive := noInduction state stackContents
          simpa [TM2.stepAux, tested, statementPushCount] using
            recursive.trans (Nat.add_le_add_left
              (Nat.le_max_right _ _) _)
      | true =>
          have recursive := yesInduction state stackContents
          simpa [TM2.stepAux, tested, statementPushCount] using
            recursive.trans (Nat.add_le_add_left
              (Nat.le_max_left _ _) _)
  | goto target => simp [TM2.stepAux, statementPushCount, TM2.stackSpace]
  | halt => simp [TM2.stepAux, statementPushCount, TM2.stackSpace]

/-- Uniform push allowance for one counted step of a finite machine.  A sum
over all labels is a convenient computable upper bound on their maximum. -/
def machinePushBound (machine : FinTM2) : Nat :=
  ∑ label, statementPushCount (machine.m label)

theorem statementPushCount_le_machinePushBound
    (machine : FinTM2) (label : machine.Λ) :
    statementPushCount (machine.m label) ≤ machinePushBound machine := by
  classical
  unfold machinePushBound
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (statementPushCount (machine.m other)))
    (Finset.mem_univ label)

/-- One counted `FinTM2` step increases total stack population by at most the
machine-wide constant. -/
theorem step_stackSpace_le (machine : FinTM2)
    {before after : machine.Cfg}
    (step : machine.step before = some after) :
    TM2.stackSpace after ≤
      TM2.stackSpace before + machinePushBound machine := by
  rcases before with ⟨label, state, stackContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      have statement := stepAux_stackSpace_le
        (machine.m label) state stackContents
      have uniform := statementPushCount_le_machinePushBound machine label
      exact statement.trans (Nat.add_le_add_left uniform _)

private theorem iterate_none {Configuration : Type}
    (transition : Configuration → Option Configuration) (steps : Nat) :
    (flip bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      exact induction

/-- After a counted run of `steps`, total stack population has grown by at
most `steps` times the fixed one-step push allowance. -/
theorem iterate_stackSpace_le (machine : FinTM2) :
    ∀ (steps : Nat) (first last : machine.Cfg),
      (flip bind machine.step)^[steps] (some first) = some last →
      TM2.stackSpace last ≤
        TM2.stackSpace first + steps * machinePushBound machine := by
  intro steps
  induction steps with
  | zero =>
      intro first last equality
      simp only [Function.iterate_zero, id_eq,
        Option.some.injEq] at equality
      subst last
      simp
  | succ steps induction =>
      intro first last equality
      rw [Function.iterate_succ_apply] at equality
      cases firstStep : machine.step first with
      | none =>
          change (flip bind machine.step)^[steps]
            (machine.step first) = some last at equality
          rw [firstStep] at equality
          rw [iterate_none] at equality
          cases equality
      | some middle =>
          change (flip bind machine.step)^[steps]
            (machine.step first) = some last at equality
          rw [firstStep] at equality
          have remainder :
              (flip bind machine.step)^[steps] (some middle) =
                some last := by
            exact equality
          have restBound := induction middle last remainder
          have stepBound := step_stackSpace_le machine firstStep
          calc
            TM2.stackSpace last ≤
                TM2.stackSpace middle +
                  steps * machinePushBound machine := restBound
            _ ≤ (TM2.stackSpace first + machinePushBound machine) +
                  steps * machinePushBound machine := by omega
            _ = TM2.stackSpace first +
                  (steps + 1) * machinePushBound machine := by
              rw [Nat.add_mul]
              omega

@[simp]
theorem stackSpace_initList (machine : FinTM2)
    (input : List (machine.Γ machine.k₀)) :
    TM2.stackSpace (initList machine input) = input.length := by
  classical
  unfold TM2.stackSpace
  rw [Fintype.sum_eq_single machine.k₀]
  · simp [initList]
  · intro stack different
    simp [initList, different]

@[simp]
theorem stackSpace_haltList (machine : FinTM2)
    (output : List (machine.Γ machine.k₁)) :
    TM2.stackSpace (haltList machine output) = output.length := by
  classical
  unfold TM2.stackSpace
  rw [Fintype.sum_eq_single machine.k₁]
  · simp [haltList]
  · intro stack different
    simp [haltList, different]

/-- Polynomial output-length envelope induced by a polynomial-time machine's
counted time bound and fixed statement-push allowance. -/
def outputLengthPolynomial
    {α β αΓ βΓ : Type}
    {encodeInput : α → List αΓ} {encodeOutput : β → List βΓ}
    {function : α → β}
    (computer : TM2ComputableInPolyTime
      encodeInput encodeOutput function) : Polynomial Nat :=
  Polynomial.X +
    computer.time * Polynomial.C (machinePushBound computer.tm)

@[simp]
theorem outputLengthPolynomial_eval
    {α β αΓ βΓ : Type}
    {encodeInput : α → List αΓ} {encodeOutput : β → List βΓ}
    {function : α → β}
    (computer : TM2ComputableInPolyTime
      encodeInput encodeOutput function) (length : Nat) :
    (outputLengthPolynomial computer).eval length =
      length + computer.time.eval length * machinePushBound computer.tm := by
  simp [outputLengthPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul]

/-- Every polynomial-time machine emits a polynomially bounded symbol stream,
independently of any semantic size analysis of its computed function. -/
theorem output_length_le_polynomial_eval
    {α β αΓ βΓ : Type}
    {encodeInput : α → List αΓ} {encodeOutput : β → List βΓ}
    {function : α → β}
    (computer : TM2ComputableInPolyTime
      encodeInput encodeOutput function) (input : α) :
    (encodeOutput (function input)).length ≤
      (outputLengthPolynomial computer).eval
        (encodeInput input).length := by
  let run := computer.outputsFun input
  have growth := iterate_stackSpace_le computer.tm run.steps
    (initList computer.tm
      (List.map computer.inputAlphabet.invFun (encodeInput input)))
    (haltList computer.tm
      (List.map computer.outputAlphabet.invFun
        (encodeOutput (function input)))) run.evals_in_steps
  rw [stackSpace_initList, stackSpace_haltList,
    List.length_map, List.length_map] at growth
  rw [outputLengthPolynomial_eval]
  exact growth.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ run.steps_le_m) _)

end TM2OutputLength

end LeanTrominoes

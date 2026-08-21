/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerExecution

/-! # Polynomial bounds for finite-state word transducers -/

namespace LeanTrominoes

open BigOperators Computability Turing

namespace FiniteStateTransducer

/-- Sum of all fixed transition-word lengths. -/
noncomputable def transitionWeight {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (transition : Control → Source → Control × List Target) : Nat :=
  ∑ control : Control, ∑ symbol : Source,
    (transition control symbol).2.length

/-- Sum of all fixed terminal-word lengths. -/
noncomputable def finishWeight {Control Target : Type}
    [Fintype Control] (finish : Control → List Target) : Nat :=
  ∑ control : Control, (finish control).length

theorem transition_length_le_weight
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (transition : Control → Source → Control × List Target)
    (control : Control) (symbol : Source) :
    (transition control symbol).2.length ≤ transitionWeight transition := by
  classical
  calc
    (transition control symbol).2.length ≤
        ∑ other : Source, (transition control other).2.length :=
      Finset.single_le_sum
        (fun other _ => Nat.zero_le
          (transition control other).2.length)
        (Finset.mem_univ symbol)
    _ ≤ ∑ other : Control, ∑ item : Source,
          (transition other item).2.length :=
      Finset.single_le_sum
        (fun other _ => Nat.zero_le
          (∑ item : Source, (transition other item).2.length))
        (Finset.mem_univ control)

theorem finish_length_le_weight
    {Control Target : Type} [Fintype Control]
    (finish : Control → List Target) (control : Control) :
    (finish control).length ≤ finishWeight finish := by
  classical
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (finish other).length)
    (Finset.mem_univ control)

/-- The transition portion emits at most a fixed multiple of input length. -/
theorem scan_output_length_le
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (transition : Control → Source → Control × List Target)
    (control : Control) (input : List Source) :
    (scan transition control input).2.length ≤
      input.length * transitionWeight transition := by
  induction input generalizing control with
  | nil => simp [scan]
  | cons symbol input induction =>
      let current := transition control symbol
      let rest := scan transition current.1 input
      have currentBound :=
        transition_length_le_weight transition control symbol
      have restBound := induction current.1
      change (current.2 ++ rest.2).length ≤
        (input.length + 1) * transitionWeight transition
      rw [List.length_append]
      calc
        current.2.length + rest.2.length ≤
            transitionWeight transition +
              input.length * transitionWeight transition :=
          Nat.add_le_add currentBound restBound
        _ = (input.length + 1) * transitionWeight transition := by
          rw [Nat.add_mul]
          omega

/-- Total output length is uniformly linear. -/
theorem output_length_le
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) :
    (output initial transition finish input).length ≤
      input.length * transitionWeight transition + finishWeight finish := by
  let scanned := scan transition initial input
  change (scanned.2 ++ finish scanned.1).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add
    (scan_output_length_le transition initial input)
    (finish_length_le_weight finish scanned.1)

noncomputable def timePolynomial
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) : Polynomial Nat :=
  Polynomial.C (transitionWeight transition + 2) * Polynomial.X +
    Polynomial.C (finishWeight finish + 3)

@[simp] theorem timePolynomial_eval
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (length : Nat) :
    (timePolynomial transition finish).eval length =
      (transitionWeight transition + 2) * length +
        finishWeight finish + 3 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]
  omega

@[simp] theorem map_refl_invFun {Symbol : Type}
    (symbols : List Symbol) :
    symbols.map (Equiv.refl Symbol).invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp only [List.map_cons]
      rw [induction]
      rfl

/-- Every fixed finite-state word transducer is polynomial-time under native
list encodings. -/
noncomputable def computableInPolyTime
    {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) :
    TM2ComputableInPolyTime id id
      (output initial transition finish) where
  tm := machine Control Source Target initial transition finish
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial transition finish
  outputsFun input := by
    have exact := outputsInExactTime initial transition finish input
    have exact' : TM2OutputsInTime
        (machine Control Source Target initial transition finish)
        (List.map (Equiv.refl Source).invFun (id input))
        (some (List.map (Equiv.refl Target).invFun
          (id (output initial transition finish input))))
        (2 * input.length +
          (output initial transition finish input).length + 3) := by
      simpa only [id_eq, map_refl_invFun] using exact
    refine
      { toEvalsTo := exact'.toEvalsTo
        steps_le_m := exact'.steps_le_m.trans ?_ }
    rw [timePolynomial_eval]
    have outputBound := output_length_le
      initial transition finish input
    calc
      2 * input.length +
          (output initial transition finish input).length + 3 ≤
        2 * input.length +
          (input.length * transitionWeight transition +
            finishWeight finish) + 3 := by omega
      _ = (transitionWeight transition + 2) * input.length +
          finishWeight finish + 3 := by ring

end FiniteStateTransducer
end LeanTrominoes

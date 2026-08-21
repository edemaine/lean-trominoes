/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineExecution
import LeanTrominoes.TM2OutputLength

/-! # Polynomial-time closure under running two compilers on one input -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

/-- The physical fork output is exactly the inverse-alphabet image of the
semantic separated-pair encoding. -/
theorem physicalSeparated_eq_encoded_pair
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (firstValue : FirstOutput) (secondValue : SecondOutput) :
    physicalSeparated first second
        (List.map first.outputAlphabet.invFun (encodeFirst firstValue))
        (List.map second.outputAlphabet.invFun (encodeSecond secondValue)) =
      List.map (outputAlphabetEquiv FirstSymbol SecondSymbol).invFun
        (SeparatedProductEncoding.encode encodeFirst encodeSecond
          (firstValue, secondValue)) := by
  simp [physicalSeparated, SeparatedProductEncoding.encode,
    outputAlphabetEquiv, List.map_append, Function.comp_def]

/-- An explicit polynomial envelope for input duplication, both component
runs, and separated output assembly. -/
def forkTimePolynomial
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction) :
    Polynomial Nat :=
  first.time + second.time +
    Polynomial.C 5 * Polynomial.X +
    Polynomial.C 4 * TM2OutputLength.outputLengthPolynomial first +
    Polynomial.C 4 * TM2OutputLength.outputLengthPolynomial second +
    Polynomial.C 9

@[simp]
theorem forkTimePolynomial_eval
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (length : Nat) :
    (forkTimePolynomial first second).eval length =
      first.time.eval length + second.time.eval length + 5 * length +
        4 * (TM2OutputLength.outputLengthPolynomial first).eval length +
        4 * (TM2OutputLength.outputLengthPolynomial second).eval length + 9 := by
  simp [forkTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

def inputAlphabetEquiv
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction) :
    (machine first second).Γ (machine first second).k₀ ≃ InputSymbol := by
  change InputSymbol ≃ InputSymbol
  exact Equiv.refl _

@[simp] theorem inputAlphabetEquiv_invFun
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (symbol : InputSymbol) :
    (inputAlphabetEquiv first second).invFun symbol = symbol := by
  rfl

@[simp] theorem map_inputAlphabetEquiv_invFun
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (symbols : List InputSymbol) :
    List.map (inputAlphabetEquiv first second).invFun symbols = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol remaining induction =>
      rw [List.map_cons, inputAlphabetEquiv_invFun first second symbol,
        induction]
      rfl

/-- Polynomial-time functions are closed under running two machines on the
same finite-alphabet input and returning a separated encoding of their pair
of results. -/
def computableInPolyTime
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction) :
    TM2ComputableInPolyTime encodeInput
      (SeparatedProductEncoding.encode encodeFirst encodeSecond)
      (fun input => (firstFunction input, secondFunction input)) where
  tm := machine first second
  inputAlphabet := inputAlphabetEquiv first second
  outputAlphabet := outputAlphabetEquiv FirstSymbol SecondSymbol
  time := forkTimePolynomial first second
  outputsFun input := by
    let raw := forkRun first second input
    have firstLengthBound :=
      TM2OutputLength.output_length_le_polynomial_eval first input
    have secondLengthBound :=
      TM2OutputLength.output_length_le_polynomial_eval second input
    refine
      { steps := raw.steps
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · rw [map_inputAlphabetEquiv_invFun first second]
      convert raw.evals_in_steps using 1
      simp only [Option.map_some, Option.some.injEq]
      congr 1
      exact (physicalSeparated_eq_encoded_pair first second
        (firstFunction input) (secondFunction input)).symm
    · have rawBound := raw.steps_le_m
      rw [forkTimePolynomial_eval]
      dsimp at rawBound firstLengthBound secondLengthBound ⊢
      omega

end TM2ForkMachine
end LeanTrominoes

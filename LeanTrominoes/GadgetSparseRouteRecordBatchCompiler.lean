/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchTimeBound

/-! # Polynomial-time compiler for canonical route-request batches -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def inputAlphabetEquiv : machine.Γ machine.k₀ ≃ InputToken :=
  Equiv.refl InputToken

def outputAlphabetEquiv : machine.Γ machine.k₁ ≃ OutputToken :=
  Equiv.refl OutputToken

@[simp] theorem map_inputAlphabetEquiv_invFun
    (symbols : List InputToken) :
    symbols.map inputAlphabetEquiv.invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp only [List.map_cons]
      rw [induction]
      rfl

@[simp] theorem map_outputAlphabetEquiv_invFun
    (symbols : List OutputToken) :
    symbols.map outputAlphabetEquiv.invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp only [List.map_cons]
      rw [induction]
      rfl

noncomputable def timePolynomial : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) *
    (Polynomial.C (Fintype.card innerCompiler.tm.K + 50) *
      (Polynomial.X + Polynomial.C 1) ^ 2 + Polynomial.C 3)

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length =
      (length + 1) * (unitCost length + 3) := by
  simp [timePolynomial, unitCost, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow]

/-- Mapping the exact complement-counter machine over a structured list of
valid requests emits their concatenated canonical record words in polynomial
time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime input id output where
  tm := machine
  inputAlphabet := inputAlphabetEquiv
  outputAlphabet := outputAlphabetEquiv
  time := timePolynomial
  outputsFun requests := by
    have run := machineRun requests
    have run' : TM2OutputsInTime machine
        (List.map inputAlphabetEquiv.invFun (input requests))
        (some (List.map outputAlphabetEquiv.invFun
          (id (output requests))))
        (runTime requests []) := by
      refine
        { steps := run.steps
          evals_in_steps := ?_
          steps_le_m := run.steps_le_m }
      change (flip bind machine.step)^[run.steps]
          (some (initList machine
            (List.map inputAlphabetEquiv.invFun
              (input requests)))) =
        some (haltList machine
          (List.map outputAlphabetEquiv.invFun
            (id (output requests))))
      rw [map_inputAlphabetEquiv_invFun,
        map_outputAlphabetEquiv_invFun]
      exact run.evals_in_steps
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (by
            rw [timePolynomial_eval]
            exact initialRunTime_le requests) }

end GadgetSparseRouteRecordBatch
end
end LeanTrominoes

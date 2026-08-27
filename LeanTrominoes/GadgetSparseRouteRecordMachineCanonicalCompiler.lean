/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalTimeBound

/-! # Polynomial-time compiler for valid canonical route requests -/

namespace LeanTrominoes

open Computability Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction.RouteRasterRequest

/-- A compact route request carrying precisely the cursor precondition used
by the low-level complement-counter machine. -/
abbrev ValidRequest :=
  { request : Request // request.metadata.CursorValid }

def validRequestInput (request : ValidRequest) : List InputToken :=
  GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock request.1

def validRequestOutput (request : ValidRequest) : List OutputToken :=
  complementRecordBlock request.1

noncomputable def canonicalTimePolynomial : Polynomial Nat :=
  Polynomial.C 16 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem canonicalTimePolynomial_eval (length : Nat) :
    canonicalTimePolynomial.eval length = 16 * (length + 1) ^ 2 := by
  simp [canonicalTimePolynomial, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_pow]

/-- The fixed route machine is a polynomial-time compiler when its semantic
input type records the canonical cursor-validity promise. -/
noncomputable def validRequestComputableInPolyTime :
    TM2ComputableInPolyTime validRequestInput id validRequestOutput where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := canonicalTimePolynomial
  outputsFun request := by
    have run := canonical_outputsInTime request.1 request.2
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl InputToken).invFun
          (validRequestInput request))
        (some (List.map (Equiv.refl OutputToken).invFun
          (id (validRequestOutput request))))
        (canonicalTotalTime request.1) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq,
        validRequestInput, validRequestOutput] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (by
            rw [canonicalTimePolynomial_eval]
            exact canonicalTotalTime_le_square request.1 request.2) }

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes

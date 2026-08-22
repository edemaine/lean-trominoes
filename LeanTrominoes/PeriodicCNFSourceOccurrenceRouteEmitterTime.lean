/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInterface
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTimeBound

/-! # Polynomial-time source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 172 * Polynomial.X ^ 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 172 * length ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_pow]

/-- Emit all counted source-occurrence route records in quadratic time in
the complete separated input encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      SourceOccurrenceRouteEmitter.Input (List OutputToken)
      InputSymbol OutputToken SourceOccurrenceRouteEmitter.encode id
      SourceOccurrenceRouteEmitter.emit where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl InputSymbol).invFun
          (SourceOccurrenceRouteEmitter.encode input))
        (some (List.map (Equiv.refl OutputToken).invFun
          (id (SourceOccurrenceRouteEmitter.emit input))))
        (totalTime input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

end

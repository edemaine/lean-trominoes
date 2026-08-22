/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupFieldScanExecution

/-! # Complete rejected fields for last-true unary lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

/-- A false row bit consumes and restores one unary field without changing
the candidate. -/
def rejectedField_evalsInTime (value : Nat)
    (tail : List UnarySymbol) (data : TapeData)
    (valuesEq : data.values =
      UnaryFieldEncoderMachine.unaryField value ++ tail) :
    EvalsToInTime machine.step (prepareValueCfg false data)
      (some (nextBitCfg
        { data with
          values := tail
          valuesRestore :=
            (UnaryFieldEncoderMachine.unaryField value).reverse ++
              data.valuesRestore }))
      (2 * value + 3) := by
  have prepared := oneStep (step_prepareValue_false data)
  have scanned := rejectedUnits_evalsInTime value tail data
    (by simpa [UnaryFieldEncoderMachine.unaryField] using valuesEq)
  have whole := EvalsToInTime.trans machine.step
    1 (2 * value + 2) _ _ _ prepared scanned
  simpa [Nat.add_assoc] using whole

end LastTrueUnaryValueLookupMachine
end LeanTrominoes

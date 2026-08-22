/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupFieldScanExecution

/-! # Complete selected fields for last-true unary lookup -/

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

/-- A true row bit replaces the previous candidate with the current unary
field while retaining a reversible copy of the field stream. -/
def selectedField_evalsInTime (value : Nat)
    (tail : List UnarySymbol) (previousCandidate : List Unit)
    (data : TapeData)
    (valuesEq : data.values =
      UnaryFieldEncoderMachine.unaryField value ++ tail)
    (candidateEq : data.candidate = previousCandidate) :
    EvalsToInTime machine.step (prepareValueCfg true data)
      (some (nextBitCfg
        { data with
          values := tail
          valuesRestore :=
            (UnaryFieldEncoderMachine.unaryField value).reverse ++
              data.valuesRestore
          candidate := List.replicate value () }))
      (previousCandidate.length + 3 * value + 4) := by
  let clearedData : TapeData := { data with candidate := [] }
  have prepared := oneStep (step_prepareValue_true data)
  have cleared := clearCandidate_evalsInTime true previousCandidate data
    candidateEq
  have cleared' : EvalsToInTime machine.step (clearCandidateCfg true data)
      (some (readValueCfg true clearedData))
      (previousCandidate.length + 1) := by
    simpa [clearedData] using cleared
  have scanned := selectedUnits_evalsInTime value tail clearedData
    (by simpa [clearedData, UnaryFieldEncoderMachine.unaryField] using valuesEq)
  have throughClear := EvalsToInTime.trans machine.step
    1 (previousCandidate.length + 1) _ _ _ prepared cleared'
  have whole := EvalsToInTime.trans machine.step
    (previousCandidate.length + 1 + 1) (3 * value + 2)
    _ _ _ throughClear scanned
  convert whole using 1
  · simp [clearedData]
  · omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes

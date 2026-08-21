/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsCleanupSteps

/-! # Clearing the cumulative unary sum -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

def clearSum_evalsInTime (symbols : List Symbol) (data : TapeData)
    (sumEq : data.sum = symbols) :
    EvalsToInTime (TM2.step program) (clearSumCfg data)
      (some (reverseOutputCfg { data with sum := [] }))
      (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearSum_nil data sumEq)
      simpa using step
  | cons symbol symbols induction =>
      let nextData : TapeData := { data with sum := symbols }
      have first := FiniteBlockTransducer.oneStep
        (step_clearSum_cons data symbol symbols sumEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (symbols.length + 1)
        (clearSumCfg data) (clearSumCfg nextData)
        (some (reverseOutputCfg { nextData with sum := [] }))
        first rest
      convert composed using 1
      simp

end UnaryPrefixSumsMachine
end LeanTrominoes

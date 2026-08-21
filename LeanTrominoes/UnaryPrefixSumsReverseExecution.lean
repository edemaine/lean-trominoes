/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsScanSteps

/-! # Reversing unary prefix-sum output -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

def reverseOutput_evalsInTime (symbols : List Symbol) (data : TapeData)
    (reverseEq : data.outputReverse = symbols) :
    EvalsToInTime (TM2.step program) (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := symbols.reverse ++ data.output }))
      (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_reverseOutput_nil data reverseEq)
      simpa using step
  | cons symbol symbols induction =>
      let nextData : TapeData :=
        { data with
          outputReverse := symbols
          output := symbol :: data.output }
      have first := FiniteBlockTransducer.oneStep
        (step_reverseOutput_cons data symbol symbols reverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (symbols.length + 1)
        (reverseOutputCfg data) (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := symbols.reverse ++ nextData.output }))
        first rest
      convert composed using 1 <;>
        simp [nextData, List.reverse_cons, List.append_assoc]

end UnaryPrefixSumsMachine
end LeanTrominoes

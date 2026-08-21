/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountSuffixSteps

/-! # Terminal cleanup for row-prefix true counts -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def clearRowIndex_evalsInTime (tokens : List Unit) (data : TapeData)
    (indexEq : data.rowIndex = tokens) :
    EvalsToInTime (TM2.step program) (clearRowIndexCfg data)
      (some (reverseOutputCfg { data with rowIndex := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearRowIndex_nil data indexEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData := { data with rowIndex := tokens }
      have first := FiniteBlockTransducer.oneStep
        (step_clearRowIndex_cons data tokens indexEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearRowIndexCfg data) (clearRowIndexCfg nextData)
        (some (reverseOutputCfg { nextData with rowIndex := [] }))
        first rest
      convert composed using 1
      simp

def reverseOutput_evalsInTime (symbols : List OutputSymbol)
    (data : TapeData) (reverseEq : data.outputReverse = symbols) :
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

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

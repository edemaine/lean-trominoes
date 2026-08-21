/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsCopyExecution

/-! # Restoring a cumulative unary sum -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

/-- Restore all copied unary markers to the cumulative-sum stack. -/
def restoreSum_evalsInTime (saved : Symbol) (symbols : List Symbol)
    (data : TapeData) (restoreEq : data.sumRestore = symbols) :
    EvalsToInTime (TM2.step program) (restoreSumCfg saved data)
      (some (consumeSavedCfg saved
        { data with
          sum := copiedUnits symbols ++ data.sum
          sumRestore := [] }))
      (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_restoreSum_nil saved data restoreEq)
      simpa [copiedUnits] using step
  | cons symbol symbols induction =>
      let nextData : TapeData :=
        { data with
          sum := .unit :: data.sum
          sumRestore := symbols }
      have first := FiniteBlockTransducer.oneStep
        (step_restoreSum_cons saved symbol symbols data restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (symbols.length + 1)
        (restoreSumCfg saved data) (restoreSumCfg saved nextData)
        (some (consumeSavedCfg saved
          { nextData with
            sum := copiedUnits symbols ++ nextData.sum
            sumRestore := [] }))
        first rest
      convert composed using 1 <;>
        simp [nextData, copiedUnits, List.reverse_cons, List.map_append,
          List.append_assoc]

end UnaryPrefixSumsMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsCoreSteps

/-! # Copying a cumulative unary sum to the output -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

/-- One unary marker for every symbol copied from the sum stack, in the order
in which the stack traversal pushes them. -/
def copiedUnits (symbols : List Symbol) : List Symbol :=
  symbols.reverse.map fun _ => .unit

/-- Copy the current cumulative sum to the reverse output and to its restore
stack, then write the field delimiter. -/
def copySum_evalsInTime (saved : Symbol) (symbols : List Symbol)
    (data : TapeData) (sumEq : data.sum = symbols) :
    EvalsToInTime (TM2.step program) (copySumCfg saved data)
      (some (restoreSumCfg saved
        { data with
          sum := []
          sumRestore := copiedUnits symbols ++ data.sumRestore
          outputReverse :=
            .delimiter :: copiedUnits symbols ++ data.outputReverse }))
      (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_copySum_nil saved data sumEq)
      simpa [copiedUnits] using step
  | cons symbol symbols induction =>
      let nextData : TapeData :=
        { data with
          sum := symbols
          sumRestore := .unit :: data.sumRestore
          outputReverse := .unit :: data.outputReverse }
      have first := FiniteBlockTransducer.oneStep
        (step_copySum_cons saved symbol symbols data sumEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (symbols.length + 1)
        (copySumCfg saved data) (copySumCfg saved nextData)
        (some (restoreSumCfg saved
          { nextData with
            sum := []
            sumRestore := copiedUnits symbols ++ nextData.sumRestore
            outputReverse :=
              .delimiter :: copiedUnits symbols ++
                nextData.outputReverse }))
        first rest
      convert composed using 1 <;>
        simp [nextData, copiedUnits, List.reverse_cons, List.map_append,
          List.append_assoc]

end UnaryPrefixSumsMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsRestoreExecution

/-! # Emitting and restoring one unary block start -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

@[simp] theorem copiedUnits_replicate_unit (count : Nat) :
    copiedUnits
        (List.replicate count UnaryFieldEncoderMachine.Symbol.unit) =
      List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  simp [copiedUnits]

/-- Emit the current unary start offset and restore it before consuming the
first symbol of the corresponding input field. -/
def emitStart_evalsInTime (saved : Symbol) (start : Nat)
    (data : TapeData)
    (sumEq : data.sum = List.replicate start .unit)
    (restoreEq : data.sumRestore = []) :
    EvalsToInTime (TM2.step program) (copySumCfg saved data)
      (some (consumeSavedCfg saved
        { data with
          sum := List.replicate start .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }))
      (2 * start + 2) := by
  let afterCopy : TapeData :=
    { data with
      sum := []
      sumRestore := List.replicate start .unit
      outputReverse :=
        .delimiter :: List.replicate start .unit ++ data.outputReverse }
  have copyRun := copySum_evalsInTime saved
    (List.replicate start UnaryFieldEncoderMachine.Symbol.unit) data sumEq
  have copyRun' :
      EvalsToInTime (TM2.step program) (copySumCfg saved data)
        (some (restoreSumCfg saved afterCopy)) (start + 1) := by
    simpa [afterCopy, restoreEq] using copyRun
  have restoreRun := restoreSum_evalsInTime saved
    (List.replicate start UnaryFieldEncoderMachine.Symbol.unit)
    afterCopy rfl
  have restoreRun' :
      EvalsToInTime (TM2.step program) (restoreSumCfg saved afterCopy)
        (some (consumeSavedCfg saved
          { data with
            sum := List.replicate start .unit
            sumRestore := []
            outputReverse :=
              .delimiter :: List.replicate start .unit ++
                data.outputReverse }))
        (start + 1) := by
    simpa [afterCopy] using restoreRun
  have composed := EvalsToInTime.trans (TM2.step program)
    (start + 1) (start + 1)
    (copySumCfg saved data) (restoreSumCfg saved afterCopy)
    (some (consumeSavedCfg saved
      { data with
        sum := List.replicate start .unit
        sumRestore := []
        outputReverse :=
          .delimiter :: List.replicate start .unit ++
            data.outputReverse }))
    copyRun' restoreRun'
  convert composed using 1
  omega

end UnaryPrefixSumsMachine
end LeanTrominoes

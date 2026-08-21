/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsIndexRestoreExecution

/-! # Complete row-index setup for last-representative filtering -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def indexSetup_evalsInTime (rowIndex : Nat) (data : TapeData)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = []) :
    EvalsToInTime (TM2.step program) (copyIndexCfg data)
      (some (skipPrefixCfg
        { data with
          rowIndex := List.replicate rowIndex ()
          indexRestore := []
          prefixCountdown := List.replicate rowIndex () }))
      (2 * rowIndex + 2) := by
  let markers := List.replicate rowIndex ()
  let copied : TapeData :=
    { data with
      rowIndex := []
      indexRestore := markers.reverse
      prefixCountdown := markers.reverse }
  have copiedRun := copyIndex_evalsInTime markers data indexEq
  have copiedRun' :
      EvalsToInTime (TM2.step program) (copyIndexCfg data)
        (some (restoreIndexCfg copied)) (rowIndex + 1) := by
    simpa [copied, markers, restoreEq, countdownEq] using copiedRun
  have restoredRun := restoreIndex_evalsInTime markers.reverse copied rfl
  have restoredRun' :
      EvalsToInTime (TM2.step program) (restoreIndexCfg copied)
        (some (skipPrefixCfg
          { data with
            rowIndex := markers
            indexRestore := []
            prefixCountdown := markers }))
        (rowIndex + 1) := by
    simpa [copied, markers] using restoredRun
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowIndex + 1) (rowIndex + 1)
    (copyIndexCfg data) (restoreIndexCfg copied)
    (some (skipPrefixCfg
      { data with
        rowIndex := markers
        indexRestore := []
        prefixCountdown := markers }))
    copiedRun' restoredRun'
  have timeEq :
      (rowIndex + 1) + (rowIndex + 1) = 2 * rowIndex + 2 := by
    omega
  rw [timeEq] at composed
  simpa [markers] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

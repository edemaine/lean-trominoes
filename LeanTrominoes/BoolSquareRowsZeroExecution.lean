/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCopyExecution
import LeanTrominoes.BoolSquareRowsCounterToRowsExecution
import LeanTrominoes.BoolSquareRowsReverseOutputExecution
import LeanTrominoes.BoolSquareRowsRowCleanupExecution

/-! # Execution on the empty Boolean square -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def zeroTime : Nat := 12

def emptyRows_evalsInTime :
    EvalsToInTime (TM2.step program)
      (startRowsCfg ⟨[], [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg [])) 4 := by
  let empty : TapeData := ⟨[], [], [], [], [], [], [], [], [], [], []⟩
  have start := oneStep (step_startRows_nil empty rfl)
  have countdown := clearRowCountdown_evalsInTime [] empty rfl
  have throughCountdown := EvalsToInTime.trans (TM2.step program)
    1 1 (startRowsCfg empty) (clearRowCountdownCfg empty)
    (some (clearRowRestoreCfg empty))
    (by simpa [empty] using start) (by simpa [empty] using countdown)
  have restore := clearRowRestore_evalsInTime [] empty rfl
  have throughRestore := EvalsToInTime.trans (TM2.step program)
    2 1 (startRowsCfg empty) (clearRowRestoreCfg empty)
    (some (reverseOutputCfg empty)) throughCountdown
    (by simpa [empty] using restore)
  have reverse := reverseOutput_evalsInTime [] []
  have whole := EvalsToInTime.trans (TM2.step program)
    3 1 (startRowsCfg empty) (reverseOutputCfg empty)
    (some (haltCfg [])) throughRestore (by simpa [empty] using reverse)
  simpa [empty] using whole

/-- The complete machine takes twelve steps on the unique side-zero input. -/
def zero_evalsInTime :
    EvalsToInTime (TM2.step program)
      (copyInputCfg ⟨[], [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg [])) zeroTime := by
  let empty : TapeData := ⟨[], [], [], [], [], [], [], [], [], [], []⟩
  let ready : TapeData := ⟨[], [], [], [()], [], [], [], [], [], [], []⟩
  have copied := copyInput_evalsInTime [] empty rfl
  have initialized := oneStep (step_initOdd empty)
  have throughInit := EvalsToInTime.trans (TM2.step program)
    1 1 (copyInputCfg empty) (initOddCfg empty)
    (some (consumeWorkCfg ready))
    (by simpa [empty, workTokens] using copied)
    (by simpa [empty, ready] using initialized)
  have exhausted := oneStep (step_consumeWork_nil ready rfl)
  have throughCount := EvalsToInTime.trans (TM2.step program)
    2 1 (copyInputCfg empty) (consumeWorkCfg ready)
    (some (clearOddCfg ready)) throughInit
    (by simpa [ready] using exhausted)
  have cleaned := counterToRows_evalsInTime [()] [] [] [] ready
    rfl rfl rfl rfl
  have throughRows := EvalsToInTime.trans (TM2.step program)
    3 (counterToRowsTime [()] [] [] [])
    (copyInputCfg empty) (clearOddCfg ready)
    (some (startRowsCfg empty)) throughCount
    (by simpa [empty, ready] using cleaned)
  have whole := EvalsToInTime.trans (TM2.step program)
    (counterToRowsTime [()] [] [] [] + 3) 4
    (copyInputCfg empty) (startRowsCfg empty)
    (some (haltCfg [])) throughRows (by simpa [empty] using emptyRows_evalsInTime)
  convert whole using 1
  simp [zeroTime, counterToRowsTime]

end BoolSquareRowsMachine
end LeanTrominoes

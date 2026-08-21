/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsOutputSteps

/-! # Execution of one complete Boolean row -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

/-- Emitting one nonempty complete row consumes three steps per bit and
leaves the row counter on its restore stack. -/
def fullRow_evalsInTime (row sourceTail : List Bool)
    (rowNe : row ≠ []) (data : TapeData)
    (sourceEq : data.source = row ++ sourceTail)
    (countdownEq : data.rowCountdown = List.replicate row.length ()) :
    EvalsToInTime (TM2.step program) (emitBitCfg data)
      (some (finishRowCfg
        { data with
          source := sourceTail
          rowCountdown := []
          rowRestore := List.replicate row.length () ++ data.rowRestore
          outputReverse := .wordEnd ::
            (row.map fun value => .bit value).reverse ++ data.outputReverse }))
      (3 * row.length) := by
  induction row generalizing data with
  | nil => exact (rowNe rfl).elim
  | cons bit row induction =>
      let afterBit : TapeData :=
        { data with
          source := row ++ sourceTail
          outputReverse := .bit bit :: data.outputReverse }
      let afterCount : TapeData :=
        { afterBit with
          rowCountdown := List.replicate row.length ()
          rowRestore := () :: data.rowRestore }
      have emitted := oneStep
        (step_emitBit_cons data bit (row ++ sourceTail) (by
          simp [sourceEq]))
      have consumed := oneStep
        (step_consumeRowCount_cons afterBit
          (List.replicate row.length ()) (by
            simp [afterBit, countdownEq, List.replicate_succ]))
      have firstTwo := EvalsToInTime.trans (TM2.step program)
        1 1
        (emitBitCfg data) (consumeRowCountCfg afterBit)
        (some (checkRowCountCfg afterCount))
        (by simpa [afterBit] using emitted)
        (by simpa [afterCount] using consumed)
      cases row with
      | nil =>
          have checked := oneStep (step_checkRowCount_nil afterCount rfl)
          have composed := EvalsToInTime.trans (TM2.step program)
            2 1
            (emitBitCfg data) (checkRowCountCfg afterCount)
            (some (finishRowCfg
              { afterCount with
                rowCountdown := []
                outputReverse := .wordEnd :: afterCount.outputReverse }))
            (by simpa using firstTwo) checked
          convert composed using 1
          · simp [afterCount, afterBit]
          · simp
      | cons next remaining =>
          have checked := oneStep
            (step_checkRowCount_cons afterCount
              (List.replicate remaining.length ()) (by
                simp [afterCount, List.replicate_succ]))
          have firstThree := EvalsToInTime.trans (TM2.step program)
            2 1
            (emitBitCfg data) (checkRowCountCfg afterCount)
            (some (emitBitCfg afterCount))
            (by simpa using firstTwo)
            (by simpa [afterCount, List.replicate_succ] using checked)
          have rest := induction (by simp) afterCount
            (by simp [afterCount, afterBit]) rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            3 (3 * (List.length (next :: remaining)))
            (emitBitCfg data) (emitBitCfg afterCount)
            (some (finishRowCfg
              { afterCount with
                source := sourceTail
                rowCountdown := []
                rowRestore :=
                  List.replicate (List.length (next :: remaining)) () ++
                    afterCount.rowRestore
                outputReverse := .wordEnd ::
                  ((next :: remaining).map fun value => .bit value).reverse ++
                    afterCount.outputReverse }))
            (by simpa using firstThree) rest
          have restoreMarkers :
              List.replicate (List.length (bit :: next :: remaining)) () ++
                  data.rowRestore =
                List.replicate (List.length (next :: remaining)) () ++
                  () :: data.rowRestore := by
            rw [show List.length (bit :: next :: remaining) =
              List.length (next :: remaining) + 1 by simp,
              List.replicate_add]
            simp [List.append_assoc]
          convert composed using 1
          · rw [restoreMarkers]
            simp [afterCount, afterBit, List.reverse_cons,
              List.append_assoc]
          · simp
            omega

end BoolSquareRowsMachine
end LeanTrominoes

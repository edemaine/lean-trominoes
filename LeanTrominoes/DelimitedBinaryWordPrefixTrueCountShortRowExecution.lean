/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountClearPrefixExecution
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountRemainderExecution

/-! # Counting a row shorter than its diagonal index -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def shortRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexGt : row.length < rowIndex)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg data)
      (some (finishRowCfg
        { data with
          input := tail
          prefixCountdown := []
          outputReverse :=
            List.replicate
              (DelimitedBinaryWordPrefixTrueCounts.count rowIndex row)
              .unit ++ data.outputReverse }))
      (rowIndex + 1) := by
  let extra := rowIndex - row.length
  let remaining := List.replicate extra ()
  have extraPos : 0 < extra := by
    simp [extra]
    omega
  have indexSplit : row.length + extra = rowIndex := by
    simp [extra]
    omega
  have countdownSplit :
      data.prefixCountdown =
        List.replicate row.length () ++ remaining := by
    rw [countdownEq, ← indexSplit, List.replicate_add]
  let afterBits : TapeData :=
    { data with
      input := .wordEnd :: tail
      prefixCountdown := remaining
      outputReverse :=
        List.replicate (row.count true) .unit ++ data.outputReverse }
  have scanned := scanPrefixWithRemainder_evalsInTime row
    (.wordEnd :: tail) remaining data inputEq countdownSplit
  have scanned' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg data)
        (some (scanPrefixCfg afterBits)) row.length := by
    simpa [afterBits] using scanned
  let leftover := List.replicate (extra - 1) ()
  have extraPred : extra - 1 + 1 = extra := by
    omega
  have remainingCons : remaining = () :: leftover := by
    simp only [remaining, leftover]
    rw [← extraPred, List.replicate_succ]
    simp
  let afterEnd : TapeData :=
    { afterBits with input := tail, prefixCountdown := leftover }
  have endStep := FiniteBlockTransducer.oneStep
    (step_scanPrefix_wordEnd afterBits tail leftover rfl
      (by simpa [remainingCons]))
  have endStep' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg afterBits)
        (some (clearPrefixCfg afterEnd)) 1 := by
    simpa [afterEnd] using endStep
  have cleared := clearPrefix_evalsInTime leftover afterEnd rfl
  have cleared' :
      EvalsToInTime (TM2.step program) (clearPrefixCfg afterEnd)
        (some (finishRowCfg
          { afterEnd with prefixCountdown := [] })) extra := by
    have leftoverTime : leftover.length + 1 = extra := by
      simp [leftover, extraPred]
    rw [leftoverTime] at cleared
    exact cleared
  have throughEnd := EvalsToInTime.trans (TM2.step program)
    1 extra
    (scanPrefixCfg afterBits) (clearPrefixCfg afterEnd)
    (some (finishRowCfg
      { afterEnd with prefixCountdown := [] }))
    endStep' cleared'
  have composed := EvalsToInTime.trans (TM2.step program)
    row.length (extra + 1)
    (scanPrefixCfg data) (scanPrefixCfg afterBits)
    (some (finishRowCfg
      { afterEnd with prefixCountdown := [] }))
    scanned' (by simpa [Nat.add_comm] using throughEnd)
  convert composed using 1
  · simp [afterEnd, afterBits,
      DelimitedBinaryWordPrefixTrueCounts.count,
      List.take_of_length_le (Nat.le_of_lt indexGt)]
  · omega

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

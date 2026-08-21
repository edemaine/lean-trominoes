/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixCleanupExecution
import LeanTrominoes.RepresentativeEqualityRowsPrefixRemainderExecution

/-! # Scanning a row shorter than its diagonal index -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Scan a complete row when its unary index exceeds its width. -/
def shortRowScan_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexGt : row.length < rowIndex)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg true data)
      (some (finishRowCfg
        (RepresentativeEqualityRows.selected rowIndex row)
        { data with
          input := tail
          prefixCountdown := []
          rowReverse :=
            .wordEnd :: (row.map .bit).reverse ++ data.rowReverse }))
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
      rowReverse := (row.map .bit).reverse ++ data.rowReverse }
  have scanned := scanPrefixWithRemainder_evalsInTime true row
    (.wordEnd :: tail) remaining data inputEq countdownSplit
  have scanned' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg true data)
        (some (scanPrefixCfg
          (RepresentativeEqualityRows.selected rowIndex row) afterBits))
        row.length := by
    simpa [afterBits, RepresentativeEqualityRows.selected,
      List.take_of_length_le (Nat.le_of_lt indexGt)] using scanned
  let leftover := List.replicate (extra - 1) ()
  have extraPred : extra - 1 + 1 = extra := by
    omega
  have remainingCons : remaining = () :: leftover := by
    simp only [remaining, leftover]
    rw [← extraPred, List.replicate_succ]
    simp
  let afterEnd : TapeData :=
    { afterBits with
      input := tail
      prefixCountdown := leftover
      rowReverse := .wordEnd :: afterBits.rowReverse }
  have endStep := oneStep
    (step_scanPrefix_wordEnd
      (RepresentativeEqualityRows.selected rowIndex row)
      afterBits tail leftover rfl (by simpa [remainingCons]))
  have endStep' :
      EvalsToInTime (TM2.step program)
        (scanPrefixCfg
          (RepresentativeEqualityRows.selected rowIndex row) afterBits)
        (some (clearPrefixCfg
          (RepresentativeEqualityRows.selected rowIndex row) afterEnd)) 1 := by
    simpa [afterEnd] using endStep
  have cleared := clearPrefix_evalsInTime
    (RepresentativeEqualityRows.selected rowIndex row) leftover afterEnd rfl
  have cleared' :
      EvalsToInTime (TM2.step program)
        (clearPrefixCfg
          (RepresentativeEqualityRows.selected rowIndex row) afterEnd)
        (some (finishRowCfg
          (RepresentativeEqualityRows.selected rowIndex row)
          { afterEnd with prefixCountdown := [] }))
        extra := by
    have leftoverTime : leftover.length + 1 = extra := by
      simp [leftover, extraPred]
    rw [leftoverTime] at cleared
    exact cleared
  have throughEnd := EvalsToInTime.trans (TM2.step program)
    1 extra
    (scanPrefixCfg
      (RepresentativeEqualityRows.selected rowIndex row) afterBits)
    (clearPrefixCfg
      (RepresentativeEqualityRows.selected rowIndex row) afterEnd)
    (some (finishRowCfg
      (RepresentativeEqualityRows.selected rowIndex row)
      { afterEnd with prefixCountdown := [] }))
    endStep' cleared'
  have composed := EvalsToInTime.trans (TM2.step program)
    row.length (extra + 1)
    (scanPrefixCfg true data)
    (scanPrefixCfg
      (RepresentativeEqualityRows.selected rowIndex row) afterBits)
    (some (finishRowCfg
      (RepresentativeEqualityRows.selected rowIndex row)
      { afterEnd with prefixCountdown := [] }))
    scanned' (by simpa [Nat.add_comm] using throughEnd)
  convert composed using 1
  · simp [afterEnd, afterBits]
  · omega

end RepresentativeEqualityRowsMachine
end LeanTrominoes

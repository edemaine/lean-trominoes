/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixCleanupExecution
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixRemainderExecution

/-! # Scanning a row shorter than its last-representative diagonal index -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def shortRowScan_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexGt : row.length < rowIndex)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (skipPrefixCfg data)
      (some (finishRowCfg
        (LastRepresentativeEqualityRows.selected rowIndex row)
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
  have scanned := skipPrefixWithRemainder_evalsInTime row
    (.wordEnd :: tail) remaining data inputEq countdownSplit
  have scanned' :
      EvalsToInTime (TM2.step program) (skipPrefixCfg data)
        (some (skipPrefixCfg afterBits)) row.length := by
    simpa [afterBits] using scanned
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
    (step_skipPrefix_wordEnd afterBits tail leftover rfl
      (by simpa [remainingCons]))
  have endStep' :
      EvalsToInTime (TM2.step program) (skipPrefixCfg afterBits)
        (some (clearPrefixCfg afterEnd)) 1 := by
    simpa [afterEnd] using endStep
  have cleared := clearPrefix_evalsInTime leftover afterEnd rfl
  have cleared' :
      EvalsToInTime (TM2.step program) (clearPrefixCfg afterEnd)
        (some (finishRowCfg true
          { afterEnd with prefixCountdown := [] })) extra := by
    have leftoverTime : leftover.length + 1 = extra := by
      simp [leftover, extraPred]
    rw [leftoverTime] at cleared
    exact cleared
  have throughEnd := EvalsToInTime.trans (TM2.step program)
    1 extra
    (skipPrefixCfg afterBits) (clearPrefixCfg afterEnd)
    (some (finishRowCfg true
      { afterEnd with prefixCountdown := [] }))
    endStep' cleared'
  have composed := EvalsToInTime.trans (TM2.step program)
    row.length (extra + 1)
    (skipPrefixCfg data) (skipPrefixCfg afterBits)
    (some (finishRowCfg true
      { afterEnd with prefixCountdown := [] }))
    scanned' (by simpa [Nat.add_comm] using throughEnd)
  have selectedTrue :
      LastRepresentativeEqualityRows.selected rowIndex row = true := by
    simp [LastRepresentativeEqualityRows.selected,
      List.drop_eq_nil_of_le (by omega : row.length ≤ rowIndex + 1)]
  convert composed using 1
  · simp [afterEnd, afterBits, selectedTrue]
  · omega

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

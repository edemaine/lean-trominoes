/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCounterCleanupExecution

/-! # Transition from square-root counting to row emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def counterToRowsTime (odd oddRestore root : List Unit)
    (sourceReverse : List Bool) : Nat :=
  sourceReverse.length + 1 +
    (root.length + 1 + (oddRestore.length + 1 + (odd.length + 1)))

/-- Clear both odd-counter stacks, move the square root to the row counter,
and restore the copied Boolean input in its original order. -/
def counterToRows_evalsInTime (odd oddRestore root : List Unit)
    (sourceReverse : List Bool) (data : TapeData)
    (oddEq : data.odd = odd)
    (oddRestoreEq : data.oddRestore = oddRestore)
    (rootEq : data.root = root)
    (sourceReverseEq : data.sourceReverse = sourceReverse) :
    EvalsToInTime (TM2.step program) (clearOddCfg data)
      (some (startRowsCfg
        { data with
          odd := []
          oddRestore := []
          root := []
          sourceReverse := []
          source := sourceReverse.reverse ++ data.source
          rowCountdown := root.reverse ++ data.rowCountdown }))
      (counterToRowsTime odd oddRestore root sourceReverse) := by
  let oddCleared : TapeData := { data with odd := [] }
  let restoreCleared : TapeData :=
    { oddCleared with oddRestore := [] }
  let rootMoved : TapeData :=
    { restoreCleared with
      root := []
      rowCountdown := root.reverse ++ restoreCleared.rowCountdown }
  have clearOddRun := clearOdd_evalsInTime odd data oddEq
  have clearRestoreRun := clearOddRestore_evalsInTime oddRestore
    oddCleared (by simp [oddCleared, oddRestoreEq])
  have throughClear := EvalsToInTime.trans (TM2.step program)
    (odd.length + 1) (oddRestore.length + 1)
    (clearOddCfg data) (clearOddRestoreCfg oddCleared)
    (some (moveRootCfg restoreCleared))
    (by simpa [oddCleared] using clearOddRun)
    (by simpa [restoreCleared] using clearRestoreRun)
  have moveRun := moveRoot_evalsInTime root restoreCleared
    (by simp [restoreCleared, oddCleared, rootEq])
  have throughMove := EvalsToInTime.trans (TM2.step program)
    (oddRestore.length + 1 + (odd.length + 1)) (root.length + 1)
    (clearOddCfg data) (moveRootCfg restoreCleared)
    (some (reverseSourceCfg rootMoved))
    throughClear (by simpa [rootMoved] using moveRun)
  have reverseRun := reverseSource_evalsInTime sourceReverse rootMoved
    (by simp [rootMoved, restoreCleared, oddCleared, sourceReverseEq])
  have whole := EvalsToInTime.trans (TM2.step program)
    (root.length + 1 + (oddRestore.length + 1 + (odd.length + 1)))
    (sourceReverse.length + 1)
    (clearOddCfg data) (reverseSourceCfg rootMoved)
    (some (startRowsCfg
      { rootMoved with
        sourceReverse := []
        source := sourceReverse.reverse ++ rootMoved.source }))
    throughMove reverseRun
  simpa [counterToRowsTime, rootMoved, restoreCleared, oddCleared] using whole

end BoolSquareRowsMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixExecution
import LeanTrominoes.LastRepresentativeEqualityRowsDiagonalSteps

/-! # Last-representative row execution with a terminal diagonal -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

/-- If the row index equals its width, prefix skipping reaches the delimiter;
the strict suffix is empty. -/
def terminalDiagonal_evalsInTime (row : List Bool) (tail : List Token)
    (data : TapeData)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate row.length ()) :
    EvalsToInTime (TM2.step program) (skipPrefixCfg data)
      (some (finishRowCfg true
        { data with
          input := tail
          prefixCountdown := []
          rowReverse :=
            .wordEnd :: (row.map .bit).reverse ++ data.rowReverse }))
      (row.length + 2) := by
  let afterPrefix : TapeData :=
    { data with
      input := .wordEnd :: tail
      prefixCountdown := []
      rowReverse := (row.map .bit).reverse ++ data.rowReverse }
  have first := skipPrefixBits_evalsInTime row (.wordEnd :: tail)
    data inputEq countdownEq
  have first' :
      EvalsToInTime (TM2.step program) (skipPrefixCfg data)
        (some (skipDiagonalCfg afterPrefix)) (row.length + 1) := by
    simpa [afterPrefix] using first
  have second := oneStep
    (step_skipDiagonal_wordEnd afterPrefix tail rfl)
  have composed := EvalsToInTime.trans (TM2.step program)
    (row.length + 1) 1
    (skipPrefixCfg data) (skipDiagonalCfg afterPrefix)
    (some (finishRowCfg true
      { afterPrefix with
        input := tail
        rowReverse := .wordEnd :: afterPrefix.rowReverse }))
    first' second
  have timeEq : 1 + (row.length + 1) = row.length + 2 := by
    omega
  rw [timeEq] at composed
  simpa [afterPrefix] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

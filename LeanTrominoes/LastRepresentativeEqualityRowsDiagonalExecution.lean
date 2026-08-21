/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsDiagonalSteps
import LeanTrominoes.LastRepresentativeEqualityRowsSuffixExecution

/-! # Execution from a row diagonal through its strict suffix -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def diagonalAndSuffix_evalsInTime (diagonal : Bool)
    (suffix : List Bool) (tail : List Token) (data : TapeData)
    (inputEq : data.input =
      .bit diagonal :: suffix.map .bit ++ .wordEnd :: tail) :
    EvalsToInTime (TM2.step program) (skipDiagonalCfg data)
      (some (finishRowCfg (!(suffix.contains true))
        { data with
          input := tail
          rowReverse :=
            .wordEnd :: (suffix.map .bit).reverse ++
              .bit diagonal :: data.rowReverse }))
      (suffix.length + 2) := by
  let afterDiagonal : TapeData :=
    { data with
      input := suffix.map .bit ++ .wordEnd :: tail
      rowReverse := .bit diagonal :: data.rowReverse }
  have first := oneStep
    (step_skipDiagonal_bit diagonal data
      (suffix.map DelimitedBinaryWords.Token.bit ++ .wordEnd :: tail)
      (by simpa using inputEq))
  have rest := scanSuffixBits_evalsInTime true suffix tail
    afterDiagonal rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (suffix.length + 1)
    (skipDiagonalCfg data) (scanSuffixCfg true afterDiagonal)
    (some (finishRowCfg (true && !(suffix.contains true))
      { afterDiagonal with
        input := tail
        rowReverse :=
          .wordEnd :: (suffix.map .bit).reverse ++
            afterDiagonal.rowReverse }))
    first rest
  have timeEq : suffix.length + 1 + 1 = suffix.length + 2 := by
    omega
  rw [timeEq] at composed
  simpa [afterDiagonal, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

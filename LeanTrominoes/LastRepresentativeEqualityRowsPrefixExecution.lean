/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixSteps

/-! # Execution of bounded prefix skipping -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

/-- Skip exactly the Boolean prefix measured by the unary countdown. -/
def skipPrefixBits_evalsInTime (bits : List Bool) (suffix : List Token)
    (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq :
      data.prefixCountdown = List.replicate bits.length ()) :
    EvalsToInTime (TM2.step program) (skipPrefixCfg data)
      (some (skipDiagonalCfg
        { data with
          input := suffix
          prefixCountdown := []
          rowReverse := (bits.map .bit).reverse ++ data.rowReverse }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := oneStep
        (step_skipPrefix_countdown_nil data countdownEq)
      simpa [inputEq, countdownEq] using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ suffix
          prefixCountdown := List.replicate bits.length ()
          rowReverse := .bit bit :: data.rowReverse }
      have first := oneStep
        (step_skipPrefix_bit bit data (bits.map .bit ++ suffix)
          (List.replicate bits.length ())
          (by simpa using inputEq)
          (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (skipPrefixCfg data) (skipPrefixCfg nextData)
        (some (skipDiagonalCfg
          { nextData with
            input := suffix
            prefixCountdown := []
            rowReverse :=
              (bits.map .bit).reverse ++ nextData.rowReverse }))
        first rest
      simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

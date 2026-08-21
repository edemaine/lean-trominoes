/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixSteps

/-! # Prefix skipping with a remaining unary countdown -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def skipPrefixWithRemainder_evalsInTime
    (bits : List Bool) (suffix : List Token) (remaining : List Unit)
    (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq :
      data.prefixCountdown =
        List.replicate bits.length () ++ remaining) :
    EvalsToInTime (TM2.step program) (skipPrefixCfg data)
      (some (skipPrefixCfg
        { data with
          input := suffix
          prefixCountdown := remaining
          rowReverse := (bits.map .bit).reverse ++ data.rowReverse }))
      bits.length := by
  induction bits generalizing data with
  | nil =>
      have run := EvalsToInTime.refl (TM2.step program)
        (skipPrefixCfg data)
      have dataEq :
          { data with
            input := suffix
            prefixCountdown := remaining
            rowReverse := data.rowReverse } = data := by
        cases data
        simp_all
      simpa [dataEq] using run
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ suffix
          prefixCountdown :=
            List.replicate bits.length () ++ remaining
          rowReverse := .bit bit :: data.rowReverse }
      have first := oneStep
        (step_skipPrefix_bit bit data (bits.map .bit ++ suffix)
          (List.replicate bits.length () ++ remaining)
          (by simpa using inputEq)
          (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 bits.length
        (skipPrefixCfg data) (skipPrefixCfg nextData)
        (some (skipPrefixCfg
          { nextData with
            input := suffix
            prefixCountdown := remaining
            rowReverse :=
              (bits.map .bit).reverse ++ nextData.rowReverse }))
        first rest
      simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

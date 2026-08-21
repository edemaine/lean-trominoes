/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixSteps

/-! # Execution of a bounded representative-row prefix scan -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Scan exactly the Boolean prefix measured by the unary countdown. -/
def scanPrefixBits_evalsInTime (representative : Bool) (bits : List Bool)
    (suffix : List Token) (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq :
      data.prefixCountdown = List.replicate bits.length ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg representative data)
      (some (scanSuffixCfg
        (representative && !(bits.contains true))
        { data with
          input := suffix
          prefixCountdown := []
          rowReverse :=
            (bits.map .bit).reverse ++ data.rowReverse }))
      (bits.length + 1) := by
  induction bits generalizing representative data with
  | nil =>
      have step := oneStep
        (step_scanPrefix_countdown_nil representative data countdownEq)
      simpa [inputEq, countdownEq] using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ suffix
          prefixCountdown := List.replicate bits.length ()
          rowReverse := .bit bit :: data.rowReverse }
      have first := oneStep
        (step_scanPrefix_bit_countdown_cons representative bit data
          (bits.map .bit ++ suffix)
          (List.replicate bits.length ())
          (by simpa using inputEq)
          (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction (if bit then false else representative)
        nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (scanPrefixCfg representative data)
        (scanPrefixCfg (if bit then false else representative) nextData)
        (some (scanSuffixCfg
          ((if bit then false else representative) &&
            !(bits.contains true))
          { nextData with
            input := suffix
            prefixCountdown := []
            rowReverse :=
              (bits.map .bit).reverse ++ nextData.rowReverse }))
        first rest
      cases bit <;>
        simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end RepresentativeEqualityRowsMachine
end LeanTrominoes

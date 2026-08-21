/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixSteps

/-! # Prefix scanning with a remaining unary countdown -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Scan Boolean bits while preserving an arbitrary countdown suffix. -/
def scanPrefixWithRemainder_evalsInTime (representative : Bool)
    (bits : List Bool) (suffix : List Token) (remaining : List Unit)
    (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq :
      data.prefixCountdown =
        List.replicate bits.length () ++ remaining) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg representative data)
      (some (scanPrefixCfg
        (representative && !(bits.contains true))
        { data with
          input := suffix
          prefixCountdown := remaining
          rowReverse :=
            (bits.map .bit).reverse ++ data.rowReverse }))
      bits.length := by
  induction bits generalizing representative data with
  | nil =>
      have run := EvalsToInTime.refl (TM2.step program)
        (scanPrefixCfg representative data)
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
        (step_scanPrefix_bit_countdown_cons representative bit data
          (bits.map .bit ++ suffix)
          (List.replicate bits.length () ++ remaining)
          (by simpa using inputEq)
          (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction (if bit then false else representative)
        nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 bits.length
        (scanPrefixCfg representative data)
        (scanPrefixCfg (if bit then false else representative) nextData)
        (some (scanPrefixCfg
          ((if bit then false else representative) &&
            !(bits.contains true))
          { nextData with
            input := suffix
            prefixCountdown := remaining
            rowReverse :=
              (bits.map .bit).reverse ++ nextData.rowReverse }))
        first rest
      cases bit <;>
        simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end RepresentativeEqualityRowsMachine
end LeanTrominoes

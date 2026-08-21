/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountPrefixSteps

/-! # Executing a bounded row-prefix true count -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

theorem replicate_unit_cons_comm (count : Nat)
    (tail : List OutputSymbol) :
    List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
        .unit :: tail =
      .unit ::
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++ tail := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

@[simp] theorem replicate_unit_add_one (count : Nat) :
    List.replicate (count + 1)
        UnaryFieldEncoderMachine.Symbol.unit =
      UnaryFieldEncoderMachine.Symbol.unit ::
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  rw [← Nat.succ_eq_add_one, List.replicate_succ]

/-- Scan exactly the Boolean prefix measured by the unary countdown. -/
def scanPrefixBits_evalsInTime (bits : List Bool) (suffix : List Token)
    (data : TapeData) (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq :
      data.prefixCountdown = List.replicate bits.length ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg data)
      (some (scanSuffixCfg
        { data with
          input := suffix
          prefixCountdown := []
          outputReverse :=
            List.replicate (bits.count true) .unit ++
              data.outputReverse }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_scanPrefix_countdown_nil data countdownEq)
      simpa [inputEq, countdownEq] using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ suffix
          prefixCountdown := List.replicate bits.length ()
          outputReverse :=
            if bit then .unit :: data.outputReverse
            else data.outputReverse }
      have first : EvalsToInTime (TM2.step program)
          (scanPrefixCfg data) (some (scanPrefixCfg nextData)) 1 := by
        cases bit
        · exact FiniteBlockTransducer.oneStep
            (step_scanPrefix_bit_false data
              (bits.map .bit ++ suffix)
              (List.replicate bits.length ())
              (by simpa using inputEq)
              (by simpa [List.replicate_succ] using countdownEq))
        · exact FiniteBlockTransducer.oneStep
            (step_scanPrefix_bit_true data
              (bits.map .bit ++ suffix)
              (List.replicate bits.length ())
              (by simpa using inputEq)
              (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (scanPrefixCfg data) (scanPrefixCfg nextData)
        (some (scanSuffixCfg
          { nextData with
            input := suffix
            prefixCountdown := []
            outputReverse :=
              List.replicate (bits.count true) .unit ++
                nextData.outputReverse }))
        first rest
      cases bit
      · simpa [nextData] using composed
      · simpa [nextData, replicate_unit_cons_comm] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

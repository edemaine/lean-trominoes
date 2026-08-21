/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountPrefixExecution

/-! # Prefix counting with a remaining unary countdown -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def scanPrefixWithRemainder_evalsInTime (bits : List Bool)
    (suffix : List Token) (remaining : List Unit) (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ suffix)
    (countdownEq : data.prefixCountdown =
      List.replicate bits.length () ++ remaining) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg data)
      (some (scanPrefixCfg
        { data with
          input := suffix
          prefixCountdown := remaining
          outputReverse :=
            List.replicate (bits.count true) .unit ++
              data.outputReverse }))
      bits.length := by
  induction bits generalizing data with
  | nil =>
      have run := EvalsToInTime.refl (TM2.step program)
        (scanPrefixCfg data)
      have dataEq :
          { data with
            input := suffix
            prefixCountdown := remaining
            outputReverse := data.outputReverse } = data := by
        cases data
        simp_all
      simpa [dataEq] using run
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with
          input := bits.map .bit ++ suffix
          prefixCountdown :=
            List.replicate bits.length () ++ remaining
          outputReverse :=
            if bit then .unit :: data.outputReverse
            else data.outputReverse }
      have first : EvalsToInTime (TM2.step program)
          (scanPrefixCfg data) (some (scanPrefixCfg nextData)) 1 := by
        cases bit
        · exact FiniteBlockTransducer.oneStep
            (step_scanPrefix_bit_false data
              (bits.map .bit ++ suffix)
              (List.replicate bits.length () ++ remaining)
              (by simpa using inputEq)
              (by simpa [List.replicate_succ] using countdownEq))
        · exact FiniteBlockTransducer.oneStep
            (step_scanPrefix_bit_true data
              (bits.map .bit ++ suffix)
              (List.replicate bits.length () ++ remaining)
              (by simpa using inputEq)
              (by simpa [List.replicate_succ] using countdownEq))
      have rest := induction nextData rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 bits.length
        (scanPrefixCfg data) (scanPrefixCfg nextData)
        (some (scanPrefixCfg
          { nextData with
            input := suffix
            prefixCountdown := remaining
            outputReverse :=
              List.replicate (bits.count true) .unit ++
                nextData.outputReverse }))
        first rest
      cases bit
      · simpa [nextData] using composed
      · simpa [nextData, replicate_unit_cons_comm] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountSuffixSteps

/-! # Executing a row suffix discard -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def scanSuffixBits_evalsInTime (bits : List Bool) (tail : List Token)
    (data : TapeData)
    (inputEq : data.input = bits.map .bit ++ .wordEnd :: tail) :
    EvalsToInTime (TM2.step program) (scanSuffixCfg data)
      (some (finishRowCfg { data with input := tail }))
      (bits.length + 1) := by
  induction bits generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_scanSuffix_wordEnd data tail inputEq)
      simpa using step
  | cons bit bits induction =>
      let nextData : TapeData :=
        { data with input := bits.map .bit ++ .wordEnd :: tail }
      have first := FiniteBlockTransducer.oneStep
        (step_scanSuffix_bit data bit
          (bits.map .bit ++ .wordEnd :: tail) (by simpa using inputEq))
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (bits.length + 1)
        (scanSuffixCfg data) (scanSuffixCfg nextData)
        (some (finishRowCfg { nextData with input := tail }))
        first rest
      simpa [nextData] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

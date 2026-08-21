/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductCleanupExecution
import LeanTrominoes.DelimitedBinaryWordPairProductReverseExecution
import LeanTrominoes.DelimitedBinaryWordPairProductSetupSteps

/-! # Final cleanup of the binary-word ordered product -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def finishTime (source : List WordToken)
    (outputReverse : List PairToken) : Nat :=
  source.length + outputReverse.length + 3

def finish_evalsInTime (source : List WordToken)
    (outputReverse : List PairToken) :
    EvalsToInTime (TM2.step program)
      (scanOuterCfg
        ⟨[], [], [], source, [], [], [], outputReverse, []⟩)
      (some (haltCfg outputReverse.reverse))
      (finishTime source outputReverse) := by
  let data : TapeData :=
    ⟨[], [], [], source, [], [], [], outputReverse, []⟩
  have scanned := oneStep (step_scanOuter_nil data rfl)
  have cleared := clearSource_evalsInTime source data rfl
  have throughClear := EvalsToInTime.trans (TM2.step program)
    1 (source.length + 1)
    (scanOuterCfg data) (clearSourceCfg data)
    (some (reverseOutputCfg { data with source := [] }))
    (by simpa [data] using scanned) cleared
  have reversed := reverseOutput_evalsInTime outputReverse []
  have composed := EvalsToInTime.trans (TM2.step program)
    (source.length + 2) (reverseTime outputReverse)
    (scanOuterCfg data)
    (reverseOutputCfg { data with source := [] })
    (some (haltCfg outputReverse.reverse))
    (by simpa using throughClear)
    (by simpa [data] using reversed)
  convert composed using 1
  simp [finishTime, reverseTime]
  omega

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes

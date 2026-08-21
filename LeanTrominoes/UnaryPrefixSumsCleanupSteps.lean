/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsTapeUpdates

/-! # Cumulative-sum cleanup steps -/

namespace LeanTrominoes

open StateTransition Turing

namespace UnaryPrefixSumsMachine

theorem step_clearSum_nil (data : TapeData) (sumEq : data.sum = []) :
    TM2.step program (clearSumCfg data) =
      some (reverseOutputCfg { data with sum := [] }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sum = [] at sumEq
  subst sum
  simp [TM2.step, program, clearSumCfg, reverseOutputCfg, cfg, tapes,
    setSaved, savedIsNone]

theorem step_clearSum_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (sumEq : data.sum = symbol :: tail) :
    TM2.step program (clearSumCfg data) =
      some (clearSumCfg { data with sum := tail }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sum = symbol :: tail at sumEq
  subst sum
  simp [TM2.step, program, clearSumCfg, cfg, tapes, setSaved,
    savedIsNone, clearState]

end UnaryPrefixSumsMachine
end LeanTrominoes

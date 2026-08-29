/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Output-reversal steps for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg data) =
      some ⟨none, .empty,
        tapes { data with outputReverse := [] }⟩ := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    emptyCfg, cfg, program, TM2.stepAux, tokenIsNone, tokenSymbol,
    clear, update_tapes_outputReverse]
  rfl

theorem step_reverseOutput_cons (data : TapeData) (token : Token)
    (remaining : List Token)
    (reverseEq : data.outputReverse = token :: remaining) :
    machine.step (reverseOutputCfg data) =
      some (pushOutputCfg token
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change outputReverse = _ at reverseEq
  subst outputReverse
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
      pushOutputCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      tokenIsNone, tokenSymbol, update_tapes_outputReverse] <;>
    rfl

theorem step_pushOutput (data : TapeData) (token : Token) :
    machine.step (pushOutputCfg token data) =
      some (reverseOutputCfg
        { data with output := token :: data.output }) := by
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushOutputCfg,
      reverseOutputCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      storedToken, clear, update_tapes_output] <;>
    rfl

end LeanTrominoes.DelimitedRouteJoin

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Stack-restoration steps for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

theorem step_restorePrefixes_cons (data : TapeData) (token : Token)
    (remaining : List Token)
    (reverseEq : data.prefixReverse = token :: remaining) :
    machine.step (restorePrefixesCfg data) =
      some (pushPrefixCfg token
        { data with prefixReverse := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change prefixReverse = _ at reverseEq
  subst prefixReverse
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, restorePrefixesCfg,
      pushPrefixCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      tokenIsNone, tokenSymbol, update_tapes_prefixReverse] <;>
    rfl

theorem step_pushPrefix (data : TapeData) (token : Token) :
    machine.step (pushPrefixCfg token data) =
      some (restorePrefixesCfg
        { data with prefixes := token :: data.prefixes }) := by
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushPrefixCfg,
      restorePrefixesCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      storedToken, clear, update_tapes_prefixes] <;>
    rfl

theorem step_restorePrefixes_nil (data : TapeData)
    (reverseEq : data.prefixReverse = []) :
    machine.step (restorePrefixesCfg data) =
      some (restoreSuffixesCfg { data with prefixReverse := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change prefixReverse = [] at reverseEq
  subst prefixReverse
  simp only [FinTM2.step, TM2.step, machine, restorePrefixesCfg,
    restoreSuffixesCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_prefixReverse]
  rfl

theorem step_restoreSuffixes_cons (data : TapeData) (token : Token)
    (remaining : List Token)
    (reverseEq : data.suffixReverse = token :: remaining) :
    machine.step (restoreSuffixesCfg data) =
      some (pushSuffixCfg token
        { data with suffixReverse := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change suffixReverse = _ at reverseEq
  subst suffixReverse
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, restoreSuffixesCfg,
      pushSuffixCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      tokenIsNone, tokenSymbol, update_tapes_suffixReverse] <;>
    rfl

theorem step_pushSuffix (data : TapeData) (token : Token) :
    machine.step (pushSuffixCfg token data) =
      some (restoreSuffixesCfg
        { data with suffixes := token :: data.suffixes }) := by
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushSuffixCfg,
      restoreSuffixesCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      storedToken, clear, update_tapes_suffixes] <;>
    rfl

theorem step_restoreSuffixes_nil (data : TapeData)
    (reverseEq : data.suffixReverse = []) :
    machine.step (restoreSuffixesCfg data) =
      some (scanPrefixCfg { data with suffixReverse := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change suffixReverse = [] at reverseEq
  subst suffixReverse
  simp only [FinTM2.step, TM2.step, machine, restoreSuffixesCfg,
    scanPrefixCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_suffixReverse]
  rfl

end LeanTrominoes.DelimitedRouteJoin

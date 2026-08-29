/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Prefix/suffix joining steps -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

theorem step_scanPrefix_nil (data : TapeData)
    (prefixEq : data.prefixes = []) :
    machine.step (scanPrefixCfg data) =
      some (cleanupPrefixesCfg { data with prefixes := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change prefixes = [] at prefixEq
  subst prefixes
  simp only [FinTM2.step, TM2.step, machine, scanPrefixCfg,
    cleanupPrefixesCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_prefixes]
  rfl

theorem step_scanPrefix_direction (data : TapeData)
    (direction : AxisDirection) (prefixes : List Token)
    (prefixEq : data.prefixes = .direction direction :: prefixes) :
    machine.step (scanPrefixCfg data) =
      some (pushPrefixTokenCfg (.direction direction)
        { data with prefixes := prefixes }) := by
  rcases data with ⟨input, prefixReverse, storedPrefixes, suffixReverse,
    suffixes, outputReverse, output⟩
  change storedPrefixes = _ at prefixEq
  subst storedPrefixes
  simp only [FinTM2.step, TM2.step, machine, scanPrefixCfg,
    pushPrefixTokenCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenIsRouteEnd, tokenSymbol, update_tapes_prefixes]
  rfl

theorem step_scanPrefix_routeEnd (data : TapeData)
    (prefixes : List Token)
    (prefixEq : data.prefixes = .routeEnd :: prefixes) :
    machine.step (scanPrefixCfg data) =
      some (scanSuffixCfg { data with prefixes := prefixes }) := by
  rcases data with ⟨input, prefixReverse, storedPrefixes, suffixReverse,
    suffixes, outputReverse, output⟩
  change storedPrefixes = _ at prefixEq
  subst storedPrefixes
  simp only [FinTM2.step, TM2.step, machine, scanPrefixCfg,
    scanSuffixCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenIsRouteEnd, tokenSymbol, clear,
    update_tapes_prefixes]
  rfl

theorem step_pushPrefixToken (data : TapeData)
    (direction : AxisDirection) :
    machine.step (pushPrefixTokenCfg (.direction direction) data) =
      some (scanPrefixCfg
        { data with outputReverse :=
            .direction direction :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushPrefixTokenCfg,
    scanPrefixCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedToken, clear, update_tapes_outputReverse]
  rfl

theorem step_scanSuffix_nil (data : TapeData)
    (suffixEq : data.suffixes = []) :
    machine.step (scanSuffixCfg data) =
      some (cleanupPrefixesCfg { data with suffixes := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change suffixes = [] at suffixEq
  subst suffixes
  simp only [FinTM2.step, TM2.step, machine, scanSuffixCfg,
    cleanupPrefixesCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_suffixes]
  rfl

theorem step_scanSuffix_cons (data : TapeData) (token : Token)
    (suffixes : List Token)
    (suffixEq : data.suffixes = token :: suffixes) :
    machine.step (scanSuffixCfg data) =
      some (pushSuffixTokenCfg token
        { data with suffixes := suffixes }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse,
    storedSuffixes, outputReverse, output⟩
  change storedSuffixes = _ at suffixEq
  subst storedSuffixes
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, scanSuffixCfg,
      pushSuffixTokenCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
      tokenIsNone, tokenSymbol, update_tapes_suffixes] <;>
    rfl

theorem step_pushSuffixToken_direction (data : TapeData)
    (direction : AxisDirection) :
    machine.step (pushSuffixTokenCfg (.direction direction) data) =
      some (scanSuffixCfg
        { data with outputReverse :=
            .direction direction :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSuffixTokenCfg,
    scanSuffixCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedToken, tokenIsRouteEnd, clear, update_tapes_outputReverse]
  rfl

theorem step_pushSuffixToken_routeEnd (data : TapeData) :
    machine.step (pushSuffixTokenCfg .routeEnd data) =
      some (scanPrefixCfg
        { data with outputReverse := .routeEnd :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSuffixTokenCfg,
    scanPrefixCfg, tokenCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedToken, tokenIsRouteEnd, clear, update_tapes_outputReverse]
  rfl

end LeanTrominoes.DelimitedRouteJoin

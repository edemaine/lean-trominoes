/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Residual-stack cleanup steps for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

theorem step_cleanupPrefixes_nil (data : TapeData)
    (prefixEq : data.prefixes = []) :
    machine.step (cleanupPrefixesCfg data) =
      some (cleanupSuffixesCfg { data with prefixes := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change prefixes = [] at prefixEq
  subst prefixes
  simp only [FinTM2.step, TM2.step, machine, cleanupPrefixesCfg,
    cleanupSuffixesCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_prefixes]
  rfl

theorem step_cleanupPrefixes_cons (data : TapeData) (token : Token)
    (prefixes : List Token)
    (prefixEq : data.prefixes = token :: prefixes) :
    machine.step (cleanupPrefixesCfg data) =
      some (cleanupPrefixesCfg { data with prefixes := prefixes }) := by
  rcases data with ⟨input, prefixReverse, storedPrefixes, suffixReverse,
    suffixes, outputReverse, output⟩
  change storedPrefixes = _ at prefixEq
  subst storedPrefixes
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupPrefixesCfg,
      emptyCfg, cfg, program, TM2.stepAux, tokenIsNone, tokenSymbol,
      clear, update_tapes_prefixes] <;>
    rfl

theorem step_cleanupSuffixes_nil (data : TapeData)
    (suffixEq : data.suffixes = []) :
    machine.step (cleanupSuffixesCfg data) =
      some (reverseOutputCfg { data with suffixes := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change suffixes = [] at suffixEq
  subst suffixes
  simp only [FinTM2.step, TM2.step, machine, cleanupSuffixesCfg,
    reverseOutputCfg, emptyCfg, cfg, program, TM2.stepAux,
    tokenIsNone, tokenSymbol, clear, update_tapes_suffixes]
  rfl

theorem step_cleanupSuffixes_cons (data : TapeData) (token : Token)
    (suffixes : List Token)
    (suffixEq : data.suffixes = token :: suffixes) :
    machine.step (cleanupSuffixesCfg data) =
      some (cleanupSuffixesCfg { data with suffixes := suffixes }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse,
    storedSuffixes, outputReverse, output⟩
  change storedSuffixes = _ at suffixEq
  subst storedSuffixes
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupSuffixesCfg,
      emptyCfg, cfg, program, TM2.stepAux, tokenIsNone, tokenSymbol,
      clear, update_tapes_suffixes] <;>
    rfl

end LeanTrominoes.DelimitedRouteJoin

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Input-parsing steps for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

theorem step_scanLeft_left (data : TapeData) (token : Token)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left token :: remaining) :
    machine.step (scanLeftCfg data) =
      some (pushPrefixReverseCfg token
        { data with input := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, emptyCfg, cfg,
      program, TM2.stepAux, inputIsNone, inputIsLeft, inputSymbol,
      update_tapes_input] <;>
    rfl

theorem step_pushPrefixReverse (data : TapeData) (token : Token) :
    machine.step (pushPrefixReverseCfg token data) =
      some (scanLeftCfg
        { data with prefixReverse := token :: data.prefixReverse }) := by
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushPrefixReverseCfg,
      scanLeftCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
      leftToken, clear, update_tapes_prefixReverse] <;>
    rfl

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, scanRightCfg,
    emptyCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsLeft,
    inputIsSeparator, inputSymbol, clear, update_tapes_input]
  rfl

theorem step_scanRight_right (data : TapeData) (token : Token)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right token :: remaining) :
    machine.step (scanRightCfg data) =
      some (pushSuffixReverseCfg token
        { data with input := remaining }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
      pushSuffixReverseCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
      inputIsNone, inputIsRight, inputSymbol, update_tapes_input] <;>
    rfl

theorem step_pushSuffixReverse (data : TapeData) (token : Token) :
    machine.step (pushSuffixReverseCfg token data) =
      some (scanRightCfg
        { data with suffixReverse := token :: data.suffixReverse }) := by
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushSuffixReverseCfg,
      scanRightCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
      rightToken, clear, update_tapes_suffixReverse] <;>
    rfl

theorem step_scanRight_nil (data : TapeData)
    (inputEq : data.input = []) :
    machine.step (scanRightCfg data) =
      some (restorePrefixesCfg { data with input := [] }) := by
  rcases data with ⟨input, prefixReverse, prefixes, suffixReverse, suffixes,
    outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    restorePrefixesCfg, emptyCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputSymbol, clear, update_tapes_input]
  rfl

end LeanTrominoes.DelimitedRouteJoin

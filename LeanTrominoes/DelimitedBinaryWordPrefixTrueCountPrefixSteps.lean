/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountIndexSteps

/-! # Prefix transitions for row-prefix true counts -/

namespace LeanTrominoes

open StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

theorem step_scanPrefix_countdown_nil (data : TapeData)
    (countdownEq : data.prefixCountdown = []) :
    TM2.step program (scanPrefixCfg data) =
      some (scanSuffixCfg { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, scanSuffixCfg, idleCfg,
    cfg, tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_scanPrefix_input_nil (data : TapeData)
    (countdown : List Unit) (inputEq : data.input = [])
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg data) =
      some (clearPrefixCfg
        { data with input := [], prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = [] at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, clearPrefixCfg, idleCfg,
    cfg, tapes, setPresent, isPresent, setToken, tokenIsNone,
    clearToken, clearPresent, initialState]

theorem step_scanPrefix_wordEnd (data : TapeData) (tail : List Token)
    (countdown : List Unit) (inputEq : data.input = .wordEnd :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg data) =
      some (clearPrefixCfg
        { data with input := tail, prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = DelimitedBinaryWords.Token.wordEnd :: tail at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, clearPrefixCfg, idleCfg,
    cfg, tapes, setPresent, isPresent, setToken, tokenIsNone,
    tokenIsEnd, clearToken, clearPresent, initialState]

theorem step_scanPrefix_bit_false (data : TapeData) (tail : List Token)
    (countdown : List Unit)
    (inputEq : data.input = .bit false :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg data) =
      some (scanPrefixCfg
        { data with input := tail, prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = DelimitedBinaryWords.Token.bit false :: tail at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, setToken, tokenIsNone, tokenIsEnd,
    tokenIsTrue, clearToken, clearPresent, initialState]

theorem step_scanPrefix_bit_true (data : TapeData) (tail : List Token)
    (countdown : List Unit)
    (inputEq : data.input = .bit true :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg data) =
      some (scanPrefixCfg
        { data with
          input := tail
          prefixCountdown := countdown
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = DelimitedBinaryWords.Token.bit true :: tail at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, setToken, tokenIsNone, tokenIsEnd,
    tokenIsTrue, clearToken, clearPresent, initialState]

theorem step_clearPrefix_nil (data : TapeData)
    (countdownEq : data.prefixCountdown = []) :
    TM2.step program (clearPrefixCfg data) =
      some (finishRowCfg { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, finishRowCfg, idleCfg,
    cfg, tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_clearPrefix_cons (data : TapeData) (countdown : List Unit)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (clearPrefixCfg data) =
      some (clearPrefixCfg
        { data with prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change prefixCountdown = () :: countdown at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

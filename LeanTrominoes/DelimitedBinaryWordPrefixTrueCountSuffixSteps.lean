/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountPrefixSteps

/-! # Suffix and cleanup transitions for row-prefix true counts -/

namespace LeanTrominoes

open StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

theorem step_scanSuffix_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanSuffixCfg data) =
      some (finishRowCfg { data with input := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanSuffixCfg, finishRowCfg, idleCfg,
    cfg, tapes, setToken, tokenIsNone, clearToken, initialState]

theorem step_scanSuffix_wordEnd (data : TapeData) (tail : List Token)
    (inputEq : data.input = .wordEnd :: tail) :
    TM2.step program (scanSuffixCfg data) =
      some (finishRowCfg { data with input := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = DelimitedBinaryWords.Token.wordEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanSuffixCfg, finishRowCfg, idleCfg,
    cfg, tapes, setToken, tokenIsNone, tokenIsEnd, clearToken,
    initialState]

theorem step_scanSuffix_bit (data : TapeData) (bit : Bool)
    (tail : List Token) (inputEq : data.input = .bit bit :: tail) :
    TM2.step program (scanSuffixCfg data) =
      some (scanSuffixCfg { data with input := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change input = DelimitedBinaryWords.Token.bit bit :: tail at inputEq
  subst input
  cases bit <;>
    simp [TM2.step, program, scanSuffixCfg, idleCfg, cfg, tapes,
      setToken, tokenIsNone, tokenIsEnd, clearToken, initialState]

theorem step_finishRow (data : TapeData) :
    TM2.step program (finishRowCfg data) =
      some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  simp [TM2.step, program, finishRowCfg, scanStartCfg, idleCfg,
    cfg, tapes, initialState]

theorem step_clearRowIndex_nil (data : TapeData)
    (indexEq : data.rowIndex = []) :
    TM2.step program (clearRowIndexCfg data) =
      some (reverseOutputCfg { data with rowIndex := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change rowIndex = [] at indexEq
  subst rowIndex
  simp [TM2.step, program, clearRowIndexCfg, reverseOutputCfg,
    idleCfg, cfg, tapes, setPresent, isPresent, clearPresent,
    initialState]

theorem step_clearRowIndex_cons (data : TapeData) (tail : List Unit)
    (indexEq : data.rowIndex = () :: tail) :
    TM2.step program (clearRowIndexCfg data) =
      some (clearRowIndexCfg { data with rowIndex := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change rowIndex = () :: tail at indexEq
  subst rowIndex
  simp [TM2.step, program, clearRowIndexCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, idleCfg,
    cfg, tapes, setOutputSymbol, outputSymbolIsNone, initialState]

theorem step_reverseOutput_cons (data : TapeData)
    (symbol : OutputSymbol) (tail : List OutputSymbol)
    (reverseEq : data.outputReverse = symbol :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := symbol :: data.output }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown,
      outputReverse, output⟩
  change outputReverse = symbol :: tail at reverseEq
  subst outputReverse
  cases symbol <;>
    simp [TM2.step, program, reverseOutputCfg, idleCfg, cfg, tapes,
      setOutputSymbol, outputSymbolIsNone, outputSymbolFromState,
      clearOutputSymbol, initialState]

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

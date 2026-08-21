/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixSteps

/-! # Suffix-scan and selection steps of the representative equality-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

theorem step_scanSuffix_input_nil (representative : Bool) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (scanSuffixCfg representative data) =
      some (finishRowCfg representative { data with input := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanSuffixCfg, finishRowCfg, cfg, tapes,
    setToken, tokenIsNone, clearToken]

theorem step_scanSuffix_wordEnd (representative : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .wordEnd :: tail) :
    TM2.step program (scanSuffixCfg representative data) =
      some (finishRowCfg representative
        { data with
          input := tail
          rowReverse := .wordEnd :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .wordEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, scanSuffixCfg, finishRowCfg, cfg, tapes,
    setToken, tokenIsNone, tokenIsEnd, tokenFromState, clearToken]

theorem step_scanSuffix_bit (representative bit : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .bit bit :: tail) :
    TM2.step program (scanSuffixCfg representative data) =
      some (scanSuffixCfg representative
        { data with
          input := tail
          rowReverse := .bit bit :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .bit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanSuffixCfg, cfg, tapes, setToken,
    tokenIsNone, tokenIsEnd, tokenFromState, clearToken]

theorem step_finishRow_true (data : TapeData) :
    TM2.step program (finishRowCfg true data) =
      some (moveSelectedToForwardCfg data) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  simp [TM2.step, program, finishRowCfg, moveSelectedToForwardCfg,
    idleCfg, cfg, isRepresentative, initialState]

theorem step_finishRow_false (data : TapeData) :
    TM2.step program (finishRowCfg false data) =
      some (clearRejectedRowCfg false data) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  simp [TM2.step, program, finishRowCfg, clearRejectedRowCfg, cfg,
    isRepresentative]

end RepresentativeEqualityRowsMachine
end LeanTrominoes

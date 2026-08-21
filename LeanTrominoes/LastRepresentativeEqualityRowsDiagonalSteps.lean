/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixSteps

/-! # Diagonal-skipping steps of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

theorem step_skipDiagonal_input_nil (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (skipDiagonalCfg data) =
      some (finishRowCfg true { data with input := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, skipDiagonalCfg, finishRowCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, clearToken, initialState]

theorem step_skipDiagonal_wordEnd (data : TapeData) (tail : List Token)
    (inputEq : data.input = .wordEnd :: tail) :
    TM2.step program (skipDiagonalCfg data) =
      some (finishRowCfg true
        { data with
          input := tail
          rowReverse := .wordEnd :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .wordEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, skipDiagonalCfg, finishRowCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, tokenIsEnd, tokenFromState, clearToken,
    initialState]

theorem step_skipDiagonal_bit (bit : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .bit bit :: tail) :
    TM2.step program (skipDiagonalCfg data) =
      some (scanSuffixCfg true
        { data with
          input := tail
          rowReverse := .bit bit :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .bit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, skipDiagonalCfg, scanSuffixCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, tokenIsEnd, tokenFromState, clearToken,
    initialState]

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsIndexSteps

/-! # Prefix-skipping steps of the last-representative row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

theorem step_skipPrefix_countdown_nil (data : TapeData)
    (countdownEq : data.prefixCountdown = []) :
    TM2.step program (skipPrefixCfg data) =
      some (skipDiagonalCfg { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, skipPrefixCfg, skipDiagonalCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_skipPrefix_input_nil (data : TapeData)
    (countdown : List Unit) (inputEq : data.input = [])
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (skipPrefixCfg data) =
      some (clearPrefixCfg
        { data with
          input := []
          prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = [] at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, skipPrefixCfg, clearPrefixCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, setToken, tokenIsNone,
    clearTokenPresent, initialState]

theorem step_skipPrefix_wordEnd (data : TapeData)
    (tail : List Token) (countdown : List Unit)
    (inputEq : data.input = .wordEnd :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (skipPrefixCfg data) =
      some (clearPrefixCfg
        { data with
          input := tail
          prefixCountdown := countdown
          rowReverse := .wordEnd :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .wordEnd :: tail at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, skipPrefixCfg, clearPrefixCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, setToken, tokenIsNone, tokenIsEnd,
    tokenFromState, clearTokenPresent, initialState]

theorem step_skipPrefix_bit (bit : Bool) (data : TapeData)
    (tail : List Token) (countdown : List Unit)
    (inputEq : data.input = .bit bit :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (skipPrefixCfg data) =
      some (skipPrefixCfg
        { data with
          input := tail
          prefixCountdown := countdown
          rowReverse := .bit bit :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = .bit bit :: tail at inputEq
  change prefixCountdown = () :: countdown at countdownEq
  subst input
  subst prefixCountdown
  simp [TM2.step, program, skipPrefixCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, setToken, tokenIsNone, tokenIsEnd,
    tokenFromState, clearTokenPresent, initialState]

theorem step_clearPrefix_nil (data : TapeData)
    (countdownEq : data.prefixCountdown = []) :
    TM2.step program (clearPrefixCfg data) =
      some (finishRowCfg true { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, finishRowCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_clearPrefix_cons (data : TapeData) (countdown : List Unit)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (clearPrefixCfg data) =
      some (clearPrefixCfg
        { data with prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = () :: countdown at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, idleCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

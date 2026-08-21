/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsIndexSteps

/-! # Prefix-scan steps of the representative equality-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

theorem step_scanPrefix_countdown_nil (representative : Bool)
    (data : TapeData) (countdownEq : data.prefixCountdown = []) :
    TM2.step program (scanPrefixCfg representative data) =
      some (scanSuffixCfg representative
        { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, scanPrefixCfg, scanSuffixCfg, cfg, tapes,
    setPresent, isPresent, clearPresent]

theorem step_scanPrefix_input_nil (representative : Bool) (data : TapeData)
    (countdown : List Unit) (inputEq : data.input = [])
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg representative data) =
      some (clearPrefixCfg representative
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
  simp [TM2.step, program, scanPrefixCfg, clearPrefixCfg, cfg, tapes,
    setPresent, isPresent, setToken, tokenIsNone, clearToken, clearPresent]

theorem step_scanPrefix_wordEnd (representative : Bool) (data : TapeData)
    (tail : List Token) (countdown : List Unit)
    (inputEq : data.input = .wordEnd :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg representative data) =
      some (clearPrefixCfg representative
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
  simp [TM2.step, program, scanPrefixCfg, clearPrefixCfg, cfg, tapes,
    setPresent, isPresent, setToken, tokenIsNone, tokenIsEnd,
    tokenFromState, clearToken, clearPresent]

theorem step_scanPrefix_bit_countdown_cons (representative bit : Bool)
    (data : TapeData) (tail : List Token) (countdown : List Unit)
    (inputEq : data.input = .bit bit :: tail)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (scanPrefixCfg representative data) =
      some (scanPrefixCfg (if bit then false else representative)
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
  cases bit <;>
    simp [TM2.step, program, scanPrefixCfg, cfg, tapes, setToken,
      tokenIsNone, tokenIsEnd, tokenFromState, setPresent, isPresent,
      inspectPrefixToken]

theorem step_clearPrefix_nil (representative : Bool) (data : TapeData)
    (countdownEq : data.prefixCountdown = []) :
    TM2.step program (clearPrefixCfg representative data) =
      some (finishRowCfg representative
        { data with prefixCountdown := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = [] at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, finishRowCfg, cfg, tapes,
    setPresent, isPresent, clearPresent]

theorem step_clearPrefix_cons (representative : Bool) (data : TapeData)
    (countdown : List Unit)
    (countdownEq : data.prefixCountdown = () :: countdown) :
    TM2.step program (clearPrefixCfg representative data) =
      some (clearPrefixCfg representative
        { data with prefixCountdown := countdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change prefixCountdown = () :: countdown at countdownEq
  subst prefixCountdown
  simp [TM2.step, program, clearPrefixCfg, cfg, tapes, setPresent,
    isPresent, clearPresent]

end RepresentativeEqualityRowsMachine
end LeanTrominoes

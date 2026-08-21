/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsSuffixSteps

/-! # Selected-row transfer steps of the representative equality-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

theorem step_moveSelectedToForward_nil (data : TapeData)
    (rowEq : data.rowReverse = []) :
    TM2.step program (moveSelectedToForwardCfg data) =
      some (moveSelectedToOutputCfg { data with rowReverse := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowReverse = [] at rowEq
  subst rowReverse
  simp [TM2.step, program, moveSelectedToForwardCfg,
    moveSelectedToOutputCfg, idleCfg, cfg, tapes, setToken, tokenIsNone,
    clearToken, initialState]

theorem step_moveSelectedToForward_cons (data : TapeData) (token : Token)
    (tail : List Token) (rowEq : data.rowReverse = token :: tail) :
    TM2.step program (moveSelectedToForwardCfg data) =
      some (moveSelectedToForwardCfg
        { data with
          rowReverse := tail
          rowForward := token :: data.rowForward }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowReverse = token :: tail at rowEq
  subst rowReverse
  simp [TM2.step, program, moveSelectedToForwardCfg, idleCfg, cfg, tapes,
    setToken, tokenIsNone, tokenFromState, clearToken, initialState]

theorem step_moveSelectedToOutput_nil (data : TapeData)
    (rowEq : data.rowForward = []) :
    TM2.step program (moveSelectedToOutputCfg data) =
      some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowForward := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowForward = [] at rowEq
  subst rowForward
  simp [TM2.step, program, moveSelectedToOutputCfg, scanStartCfg, idleCfg,
    cfg, tapes, setToken, tokenIsNone, clearToken, initialState]

theorem step_moveSelectedToOutput_cons (data : TapeData) (token : Token)
    (tail : List Token) (rowEq : data.rowForward = token :: tail) :
    TM2.step program (moveSelectedToOutputCfg data) =
      some (moveSelectedToOutputCfg
        { data with
          rowForward := tail
          outputReverse := token :: data.outputReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowForward = token :: tail at rowEq
  subst rowForward
  simp [TM2.step, program, moveSelectedToOutputCfg, idleCfg, cfg, tapes,
    setToken, tokenIsNone, tokenFromState, clearToken, initialState]

end RepresentativeEqualityRowsMachine
end LeanTrominoes

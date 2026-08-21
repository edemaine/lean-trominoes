/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsTapeUpdates

/-! # Row-index steps of the representative equality-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

theorem step_scanStart_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanStartCfg data) =
      some (clearRowIndexCfg { data with input := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanStartCfg, clearRowIndexCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, clearToken, initialState]

theorem step_scanStart_cons (data : TapeData) (token : Token)
    (tail : List Token) (inputEq : data.input = token :: tail) :
    TM2.step program (scanStartCfg data) =
      some (copyIndexCfg
        { data with
          input := tail
          rowReverse := token :: data.rowReverse }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanStartCfg, copyIndexCfg, idleCfg, cfg,
    tapes, setToken, tokenIsNone, tokenFromState, beginRow, initialState]

theorem step_copyIndex_nil (data : TapeData)
    (indexEq : data.rowIndex = []) :
    TM2.step program (copyIndexCfg data) =
      some (restoreIndexCfg { data with rowIndex := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowIndex = [] at indexEq
  subst rowIndex
  simp [TM2.step, program, copyIndexCfg, restoreIndexCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_copyIndex_cons (data : TapeData) (tail : List Unit)
    (indexEq : data.rowIndex = () :: tail) :
    TM2.step program (copyIndexCfg data) =
      some (copyIndexCfg
        { data with
          rowIndex := tail
          indexRestore := () :: data.indexRestore
          prefixCountdown := () :: data.prefixCountdown }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change rowIndex = () :: tail at indexEq
  subst rowIndex
  simp [TM2.step, program, copyIndexCfg, idleCfg, cfg, tapes, setPresent,
    isPresent, clearPresent, initialState]

theorem step_restoreIndex_nil (data : TapeData)
    (restoreEq : data.indexRestore = []) :
    TM2.step program (restoreIndexCfg data) =
      some (scanPrefixCfg true { data with indexRestore := [] }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change indexRestore = [] at restoreEq
  subst indexRestore
  simp [TM2.step, program, restoreIndexCfg, scanPrefixCfg, idleCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_restoreIndex_cons (data : TapeData) (tail : List Unit)
    (restoreEq : data.indexRestore = () :: tail) :
    TM2.step program (restoreIndexCfg data) =
      some (restoreIndexCfg
        { data with
          rowIndex := () :: data.rowIndex
          indexRestore := tail }) := by
  rcases data with
    ⟨input, rowIndex, indexRestore, prefixCountdown, rowReverse,
      rowForward, outputReverse, output⟩
  change indexRestore = () :: tail at restoreEq
  subst indexRestore
  simp [TM2.step, program, restoreIndexCfg, idleCfg, cfg, tapes, setPresent,
    isPresent, clearPresent, initialState]

end RepresentativeEqualityRowsMachine
end LeanTrominoes

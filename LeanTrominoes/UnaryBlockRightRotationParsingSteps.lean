/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationTapes

/-! # Parsing steps for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

theorem step_scanLeft_left (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    machine.step (scanLeftCfg data) =
      some (pushSizeReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, emptyCfg, cfg,
    program, TM2.stepAux, inputIsNone, inputIsLeft, inputSymbol,
    update_tapes_input]
  rfl

theorem step_pushSizeReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSizeReverseCfg symbol data) =
      some (scanLeftCfg
        { data with sizesReverse := symbol :: data.sizesReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSizeReverseCfg,
    scanLeftCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    leftSymbol, clear, update_tapes_sizesReverse]
  rfl

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, scanRightCfg,
    emptyCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsLeft,
    inputIsSeparator, inputSymbol, clear, update_tapes_input]
  rfl

theorem step_scanRight_right (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanRightCfg data) =
      some (pushStartReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    pushStartReverseCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputIsRight, inputSymbol, update_tapes_input]
  rfl

theorem step_pushStartReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushStartReverseCfg symbol data) =
      some (scanRightCfg
        { data with startsReverse := symbol :: data.startsReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushStartReverseCfg,
    scanRightCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    rightSymbol, clear, update_tapes_startsReverse]
  rfl

theorem step_scanRight_nil (data : TapeData) (inputEq : data.input = []) :
    machine.step (scanRightCfg data) =
      some (restoreSizesCfg { data with input := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    restoreSizesCfg, emptyCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputSymbol, clear, update_tapes_input]
  rfl

theorem step_restoreSizes_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.sizesReverse = symbol :: remaining) :
    machine.step (restoreSizesCfg data) =
      some (pushSizeCfg symbol { data with sizesReverse := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change sizesReverse = _ at reverseEq
  subst sizesReverse
  simp only [FinTM2.step, TM2.step, machine, restoreSizesCfg,
    pushSizeCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, update_tapes_sizesReverse]
  rfl

theorem step_pushSize (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSizeCfg symbol data) =
      some (restoreSizesCfg { data with sizes := symbol :: data.sizes }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSizeCfg,
    restoreSizesCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedUnary, clear, update_tapes_sizes]
  rfl

theorem step_restoreSizes_nil (data : TapeData)
    (reverseEq : data.sizesReverse = []) :
    machine.step (restoreSizesCfg data) =
      some (restoreStartsCfg { data with sizesReverse := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change sizesReverse = [] at reverseEq
  subst sizesReverse
  simp only [FinTM2.step, TM2.step, machine, restoreSizesCfg,
    restoreStartsCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_sizesReverse]
  rfl

theorem step_restoreStarts_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.startsReverse = symbol :: remaining) :
    machine.step (restoreStartsCfg data) =
      some (pushStartCfg symbol { data with startsReverse := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startsReverse = _ at reverseEq
  subst startsReverse
  simp only [FinTM2.step, TM2.step, machine, restoreStartsCfg,
    pushStartCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, update_tapes_startsReverse]
  rfl

theorem step_pushStart (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushStartCfg symbol data) =
      some (restoreStartsCfg { data with starts := symbol :: data.starts }) := by
  simp only [FinTM2.step, TM2.step, machine, pushStartCfg,
    restoreStartsCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedUnary, clear, update_tapes_starts]
  rfl

theorem step_restoreStarts_nil (data : TapeData)
    (reverseEq : data.startsReverse = []) :
    machine.step (restoreStartsCfg data) =
      some (scanSizeFieldCfg { data with startsReverse := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startsReverse = [] at reverseEq
  subst startsReverse
  simp only [FinTM2.step, TM2.step, machine, restoreStartsCfg,
    scanSizeFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_startsReverse]
  rfl

end LeanTrominoes.UnaryBlockRightRotationMachine

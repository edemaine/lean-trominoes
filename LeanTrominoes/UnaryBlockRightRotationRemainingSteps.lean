/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationTapes

/-! # Remaining-output steps for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

theorem step_beginRemaining_nil (data : TapeData)
    (remainingEq : data.groupRemaining = []) :
    machine.step (beginRemainingCfg data) =
      some (clearStartCfg { data with groupRemaining := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change groupRemaining = [] at remainingEq
  subst groupRemaining
  simp only [FinTM2.step, TM2.step, machine, beginRemainingCfg,
    clearStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_groupRemaining]
  rfl

theorem step_beginRemaining_cons (data : TapeData)
    (remaining : List Unit)
    (remainingEq : data.groupRemaining = () :: remaining) :
    machine.step (beginRemainingCfg data) =
      some (copyRemainingStartCfg
        { data with groupRemaining := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change groupRemaining = _ at remainingEq
  subst groupRemaining
  simp only [FinTM2.step, TM2.step, machine, beginRemainingCfg,
    copyRemainingStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_groupRemaining]
  rfl

theorem step_copyRemainingStart_nil (data : TapeData)
    (startEq : data.start = []) :
    machine.step (copyRemainingStartCfg data) =
      some (restoreRemainingStartCfg { data with start := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = [] at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, copyRemainingStartCfg,
    restoreRemainingStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_start]
  rfl

theorem step_copyRemainingStart_cons (data : TapeData)
    (remaining : List Unit) (startEq : data.start = () :: remaining) :
    machine.step (copyRemainingStartCfg data) =
      some (copyRemainingStartCfg
        { data with
          start := remaining
          startRestore := () :: data.startRestore
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = _ at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, copyRemainingStartCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_start, update_tapes_startRestore,
    update_tapes_outputReverse]
  rfl

theorem step_restoreRemainingStart_nil (data : TapeData)
    (restoreEq : data.startRestore = []) :
    machine.step (restoreRemainingStartCfg data) =
      some (copyPositionCfg { data with startRestore := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startRestore = [] at restoreEq
  subst startRestore
  simp only [FinTM2.step, TM2.step, machine, restoreRemainingStartCfg,
    copyPositionCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_startRestore]
  rfl

theorem step_restoreRemainingStart_cons (data : TapeData)
    (remaining : List Unit)
    (restoreEq : data.startRestore = () :: remaining) :
    machine.step (restoreRemainingStartCfg data) =
      some (restoreRemainingStartCfg
        { data with
          startRestore := remaining
          start := () :: data.start }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startRestore = _ at restoreEq
  subst startRestore
  simp only [FinTM2.step, TM2.step, machine, restoreRemainingStartCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_startRestore, update_tapes_start]
  rfl

theorem step_copyPosition_nil (data : TapeData)
    (positionEq : data.position = []) :
    machine.step (copyPositionCfg data) =
      some (restorePositionCfg { data with position := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change position = [] at positionEq
  subst position
  simp only [FinTM2.step, TM2.step, machine, copyPositionCfg,
    restorePositionCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_position]
  rfl

theorem step_copyPosition_cons (data : TapeData) (remaining : List Unit)
    (positionEq : data.position = () :: remaining) :
    machine.step (copyPositionCfg data) =
      some (copyPositionCfg
        { data with
          position := remaining
          positionRestore := () :: data.positionRestore
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change position = _ at positionEq
  subst position
  simp only [FinTM2.step, TM2.step, machine, copyPositionCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_position, update_tapes_positionRestore,
    update_tapes_outputReverse]
  rfl

theorem step_restorePosition_nil (data : TapeData)
    (restoreEq : data.positionRestore = []) :
    machine.step (restorePositionCfg data) =
      some (emitRemainingDelimiterCfg
        { data with positionRestore := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change positionRestore = [] at restoreEq
  subst positionRestore
  simp only [FinTM2.step, TM2.step, machine, restorePositionCfg,
    emitRemainingDelimiterCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_positionRestore]
  rfl

theorem step_restorePosition_cons (data : TapeData)
    (remaining : List Unit)
    (restoreEq : data.positionRestore = () :: remaining) :
    machine.step (restorePositionCfg data) =
      some (restorePositionCfg
        { data with
          positionRestore := remaining
          position := () :: data.position }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change positionRestore = _ at restoreEq
  subst positionRestore
  simp only [FinTM2.step, TM2.step, machine, restorePositionCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_positionRestore, update_tapes_position]
  rfl

theorem step_emitRemainingDelimiter (data : TapeData) :
    machine.step (emitRemainingDelimiterCfg data) =
      some (beginRemainingCfg
        { data with
          position := () :: data.position
          outputReverse := .delimiter :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, emitRemainingDelimiterCfg,
    beginRemainingCfg, emptyCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse, update_tapes_position]
  rfl

theorem step_clearStart_nil (data : TapeData) (startEq : data.start = []) :
    machine.step (clearStartCfg data) =
      some (clearPositionCfg { data with start := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = [] at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, clearStartCfg,
    clearPositionCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_start]
  rfl

theorem step_clearStart_cons (data : TapeData) (remaining : List Unit)
    (startEq : data.start = () :: remaining) :
    machine.step (clearStartCfg data) =
      some (clearStartCfg { data with start := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = _ at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, clearStartCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol,
    clear, update_tapes_start]
  rfl

theorem step_clearPosition_nil (data : TapeData)
    (positionEq : data.position = []) :
    machine.step (clearPositionCfg data) =
      some (scanSizeFieldCfg { data with position := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change position = [] at positionEq
  subst position
  simp only [FinTM2.step, TM2.step, machine, clearPositionCfg,
    scanSizeFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_position]
  rfl

theorem step_clearPosition_cons (data : TapeData) (remaining : List Unit)
    (positionEq : data.position = () :: remaining) :
    machine.step (clearPositionCfg data) =
      some (clearPositionCfg { data with position := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change position = _ at positionEq
  subst position
  simp only [FinTM2.step, TM2.step, machine, clearPositionCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol,
    clear, update_tapes_position]
  rfl

end LeanTrominoes.UnaryBlockRightRotationMachine

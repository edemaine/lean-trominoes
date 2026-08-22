/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationTapes

/-! # First-output steps for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

theorem step_copyFirstStart_nil (data : TapeData)
    (startEq : data.start = []) :
    machine.step (copyFirstStartCfg data) =
      some (restoreFirstStartCfg { data with start := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = [] at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, copyFirstStartCfg,
    restoreFirstStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_start]
  rfl

theorem step_copyFirstStart_cons (data : TapeData) (remaining : List Unit)
    (startEq : data.start = () :: remaining) :
    machine.step (copyFirstStartCfg data) =
      some (copyFirstStartCfg
        { data with
          start := remaining
          startRestore := () :: data.startRestore
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change start = _ at startEq
  subst start
  simp only [FinTM2.step, TM2.step, machine, copyFirstStartCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_start, update_tapes_startRestore,
    update_tapes_outputReverse]
  rfl

theorem step_restoreFirstStart_nil (data : TapeData)
    (restoreEq : data.startRestore = []) :
    machine.step (restoreFirstStartCfg data) =
      some (copyFirstGroupCfg { data with startRestore := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startRestore = [] at restoreEq
  subst startRestore
  simp only [FinTM2.step, TM2.step, machine, restoreFirstStartCfg,
    copyFirstGroupCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_startRestore]
  rfl

theorem step_restoreFirstStart_cons (data : TapeData)
    (remaining : List Unit)
    (restoreEq : data.startRestore = () :: remaining) :
    machine.step (restoreFirstStartCfg data) =
      some (restoreFirstStartCfg
        { data with
          startRestore := remaining
          start := () :: data.start }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change startRestore = _ at restoreEq
  subst startRestore
  simp only [FinTM2.step, TM2.step, machine, restoreFirstStartCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_startRestore, update_tapes_start]
  rfl

theorem step_copyFirstGroup_nil (data : TapeData)
    (groupEq : data.group = []) :
    machine.step (copyFirstGroupCfg data) =
      some (emitFirstDelimiterCfg { data with group := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change group = [] at groupEq
  subst group
  simp only [FinTM2.step, TM2.step, machine, copyFirstGroupCfg,
    emitFirstDelimiterCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_group]
  rfl

theorem step_copyFirstGroup_cons (data : TapeData)
    (remaining : List Unit) (groupEq : data.group = () :: remaining) :
    machine.step (copyFirstGroupCfg data) =
      some (copyFirstGroupCfg
        { data with
          group := remaining
          groupRemaining := () :: data.groupRemaining
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change group = _ at groupEq
  subst group
  simp only [FinTM2.step, TM2.step, machine, copyFirstGroupCfg,
    emptyCfg, cfg, program, TM2.stepAux, unitIsNone, unitSymbol, clear,
    update_tapes_group, update_tapes_groupRemaining,
    update_tapes_outputReverse]
  rfl

theorem step_emitFirstDelimiter (data : TapeData) :
    machine.step (emitFirstDelimiterCfg data) =
      some (beginRemainingCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, emitFirstDelimiterCfg,
    beginRemainingCfg, emptyCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

end LeanTrominoes.UnaryBlockRightRotationMachine

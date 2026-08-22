/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationTapes

/-! # Input-field steps for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

theorem step_scanSizeField_nil (data : TapeData) (sizesEq : data.sizes = []) :
    machine.step (scanSizeFieldCfg data) =
      some (reverseOutputCfg { data with sizes := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change sizes = [] at sizesEq
  subst sizes
  simp only [FinTM2.step, TM2.step, machine, scanSizeFieldCfg,
    reverseOutputCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_sizes]
  rfl

theorem step_scanSizeField_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    machine.step (scanSizeFieldCfg data) =
      some (pushGroupUnitCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp only [FinTM2.step, TM2.step, machine, scanSizeFieldCfg,
    pushGroupUnitCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, update_tapes_sizes]
  rfl

theorem step_scanSizeField_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .delimiter :: remaining) :
    machine.step (scanSizeFieldCfg data) =
      some (scanStartFieldCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp only [FinTM2.step, TM2.step, machine, scanSizeFieldCfg,
    scanStartFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_sizes]
  rfl

theorem step_pushGroupUnit (data : TapeData) :
    machine.step (pushGroupUnitCfg data) =
      some (scanSizeFieldCfg
        { data with group := () :: data.group }) := by
  simp only [FinTM2.step, TM2.step, machine, pushGroupUnitCfg,
    scanSizeFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    clear, update_tapes_group]
  rfl

theorem step_scanStartField_nil (data : TapeData)
    (startsEq : data.starts = []) :
    machine.step (scanStartFieldCfg data) =
      some (beginGroupCfg { data with starts := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change starts = [] at startsEq
  subst starts
  simp only [FinTM2.step, TM2.step, machine, scanStartFieldCfg,
    beginGroupCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_starts]
  rfl

theorem step_scanStartField_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (startsEq : data.starts = .unit :: remaining) :
    machine.step (scanStartFieldCfg data) =
      some (pushStartUnitCfg { data with starts := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change starts = _ at startsEq
  subst starts
  simp only [FinTM2.step, TM2.step, machine, scanStartFieldCfg,
    pushStartUnitCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, update_tapes_starts]
  rfl

theorem step_scanStartField_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (startsEq : data.starts = .delimiter :: remaining) :
    machine.step (scanStartFieldCfg data) =
      some (beginGroupCfg { data with starts := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change starts = _ at startsEq
  subst starts
  simp only [FinTM2.step, TM2.step, machine, scanStartFieldCfg,
    beginGroupCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_starts]
  rfl

theorem step_pushStartUnit (data : TapeData) :
    machine.step (pushStartUnitCfg data) =
      some (scanStartFieldCfg { data with start := () :: data.start }) := by
  simp only [FinTM2.step, TM2.step, machine, pushStartUnitCfg,
    scanStartFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    clear, update_tapes_start]
  rfl

theorem step_beginGroup_nil (data : TapeData) (groupEq : data.group = []) :
    machine.step (beginGroupCfg data) =
      some (clearStartCfg { data with group := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change group = [] at groupEq
  subst group
  simp only [FinTM2.step, TM2.step, machine, beginGroupCfg,
    clearStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_group]
  rfl

theorem step_beginGroup_cons (data : TapeData) (remaining : List Unit)
    (groupEq : data.group = () :: remaining) :
    machine.step (beginGroupCfg data) =
      some (copyFirstStartCfg { data with group := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change group = _ at groupEq
  subst group
  simp only [FinTM2.step, TM2.step, machine, beginGroupCfg,
    copyFirstStartCfg, emptyCfg, cfg, program, TM2.stepAux,
    unitIsNone, unitSymbol, clear, update_tapes_group]
  rfl

end LeanTrominoes.UnaryBlockRightRotationMachine

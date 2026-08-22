/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Second-field steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_scanSecondField_nil (data : TapeData)
    (secondsEq : data.seconds = []) :
    machine.step (scanSecondFieldCfg data) =
      some (emitDelimiterCfg { data with seconds := [] }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change seconds = [] at secondsEq
  subst seconds
  simp only [FinTM2.step, TM2.step, machine, scanSecondFieldCfg,
    emitDelimiterCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_seconds]
  rfl

theorem step_scanSecondField_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (secondsEq : data.seconds = .unit :: remaining) :
    machine.step (scanSecondFieldCfg data) =
      some (pushSecondUnitCfg { data with seconds := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change seconds = _ at secondsEq
  subst seconds
  simp only [FinTM2.step, TM2.step, machine, scanSecondFieldCfg,
    pushSecondUnitCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_seconds]
  rfl

theorem step_scanSecondField_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (secondsEq : data.seconds = .delimiter :: remaining) :
    machine.step (scanSecondFieldCfg data) =
      some (emitDelimiterCfg { data with seconds := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change seconds = _ at secondsEq
  subst seconds
  simp only [FinTM2.step, TM2.step, machine, scanSecondFieldCfg,
    emitDelimiterCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_seconds]
  rfl

theorem step_pushSecondUnit (data : TapeData) :
    machine.step (pushSecondUnitCfg data) =
      some (scanSecondFieldCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSecondUnitCfg,
    scanSecondFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

theorem step_emitDelimiter (data : TapeData) :
    machine.step (emitDelimiterCfg data) =
      some (scanFirstFieldCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, emitDelimiterCfg,
    scanFirstFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

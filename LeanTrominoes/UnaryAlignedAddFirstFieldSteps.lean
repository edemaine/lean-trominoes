/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # First-field steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_scanFirstField_nil (data : TapeData)
    (firstsEq : data.firsts = []) :
    machine.step (scanFirstFieldCfg data) =
      some (reverseOutputCfg { data with firsts := [] }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change firsts = [] at firstsEq
  subst firsts
  simp only [FinTM2.step, TM2.step, machine, scanFirstFieldCfg,
    reverseOutputCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_firsts]
  rfl

theorem step_scanFirstField_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (firstsEq : data.firsts = .unit :: remaining) :
    machine.step (scanFirstFieldCfg data) =
      some (pushFirstUnitCfg { data with firsts := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change firsts = _ at firstsEq
  subst firsts
  simp only [FinTM2.step, TM2.step, machine, scanFirstFieldCfg,
    pushFirstUnitCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_firsts]
  rfl

theorem step_scanFirstField_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (firstsEq : data.firsts = .delimiter :: remaining) :
    machine.step (scanFirstFieldCfg data) =
      some (scanSecondFieldCfg { data with firsts := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change firsts = _ at firstsEq
  subst firsts
  simp only [FinTM2.step, TM2.step, machine, scanFirstFieldCfg,
    scanSecondFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unaryIsUnit, unarySymbol, clear, update_tapes_firsts]
  rfl

theorem step_pushFirstUnit (data : TapeData) :
    machine.step (pushFirstUnitCfg data) =
      some (scanFirstFieldCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushFirstUnitCfg,
    scanFirstFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

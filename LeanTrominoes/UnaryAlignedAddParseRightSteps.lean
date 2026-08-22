/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Right-input parsing steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_scanRight_right (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanRightCfg data) =
      some (pushSecondReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    pushSecondReverseCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputIsRight, inputSymbol, update_tapes_input]
  rfl

theorem step_pushSecondReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSecondReverseCfg symbol data) =
      some (scanRightCfg
        { data with secondReverse := symbol :: data.secondReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSecondReverseCfg,
    scanRightCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    rightSymbol, clear, update_tapes_secondReverse]
  rfl

theorem step_scanRight_nil (data : TapeData) (inputEq : data.input = []) :
    machine.step (scanRightCfg data) =
      some (restoreFirstsCfg { data with input := [] }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    restoreFirstsCfg, emptyCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputSymbol, clear, update_tapes_input]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

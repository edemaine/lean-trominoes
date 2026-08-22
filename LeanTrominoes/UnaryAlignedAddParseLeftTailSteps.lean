/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Remaining left-input parsing steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_pushFirstReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushFirstReverseCfg symbol data) =
      some (scanLeftCfg
        { data with firstReverse := symbol :: data.firstReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, pushFirstReverseCfg,
    scanLeftCfg, inputCfg, emptyCfg, cfg, program, TM2.stepAux,
    leftSymbol, clear, update_tapes_firstReverse]
  rfl

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, scanRightCfg,
    emptyCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsLeft,
    inputIsSeparator, inputSymbol, clear, update_tapes_input]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Parsing steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_scanLeft_left (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    machine.step (scanLeftCfg data) =
      some (pushFirstReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, emptyCfg, cfg,
    program, TM2.stepAux, inputIsNone, inputIsLeft, inputSymbol,
    update_tapes_input]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

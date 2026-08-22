/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationTapes

/-! # Output-reversal steps for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    haltDataCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_outputReverse]
  rfl

theorem step_reverseOutput_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.outputReverse = symbol :: remaining) :
    machine.step (reverseOutputCfg data) =
      some (pushOutputCfg symbol
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, sizesReverse, sizes, startsReverse, starts,
    group, groupRemaining, start, startRestore, position, positionRestore,
    outputReverse, output⟩
  change outputReverse = _ at reverseEq
  subst outputReverse
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
      pushOutputCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
      unaryIsNone, unarySymbol, update_tapes_outputReverse] <;>
    rfl

theorem step_pushOutput (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushOutputCfg symbol data) =
      some (reverseOutputCfg { data with output := symbol :: data.output }) := by
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, pushOutputCfg,
      reverseOutputCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
      storedUnary, clear, update_tapes_output] <;>
    rfl

end LeanTrominoes.UnaryBlockRightRotationMachine

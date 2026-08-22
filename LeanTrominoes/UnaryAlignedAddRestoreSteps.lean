/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Stack-restoration steps for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

theorem step_restoreFirsts_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.firstReverse = symbol :: remaining) :
    machine.step (restoreFirstsCfg data) =
      some (pushFirstCfg symbol { data with firstReverse := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change firstReverse = _ at reverseEq
  subst firstReverse
  simp only [FinTM2.step, TM2.step, machine, restoreFirstsCfg,
    pushFirstCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, update_tapes_firstReverse]
  rfl

theorem step_pushFirst (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushFirstCfg symbol data) =
      some (restoreFirstsCfg { data with firsts := symbol :: data.firsts }) := by
  simp only [FinTM2.step, TM2.step, machine, pushFirstCfg,
    restoreFirstsCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedUnary, clear, update_tapes_firsts]
  rfl

theorem step_restoreFirsts_nil (data : TapeData)
    (reverseEq : data.firstReverse = []) :
    machine.step (restoreFirstsCfg data) =
      some (restoreSecondsCfg { data with firstReverse := [] }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change firstReverse = [] at reverseEq
  subst firstReverse
  simp only [FinTM2.step, TM2.step, machine, restoreFirstsCfg,
    restoreSecondsCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_firstReverse]
  rfl

theorem step_restoreSeconds_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.secondReverse = symbol :: remaining) :
    machine.step (restoreSecondsCfg data) =
      some (pushSecondCfg symbol { data with secondReverse := remaining }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change secondReverse = _ at reverseEq
  subst secondReverse
  simp only [FinTM2.step, TM2.step, machine, restoreSecondsCfg,
    pushSecondCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, update_tapes_secondReverse]
  rfl

theorem step_pushSecond (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSecondCfg symbol data) =
      some (restoreSecondsCfg { data with seconds := symbol :: data.seconds }) := by
  simp only [FinTM2.step, TM2.step, machine, pushSecondCfg,
    restoreSecondsCfg, unaryCfg, emptyCfg, cfg, program, TM2.stepAux,
    storedUnary, clear, update_tapes_seconds]
  rfl

theorem step_restoreSeconds_nil (data : TapeData)
    (reverseEq : data.secondReverse = []) :
    machine.step (restoreSecondsCfg data) =
      some (scanFirstFieldCfg { data with secondReverse := [] }) := by
  rcases data with ⟨input, firstReverse, firsts, secondReverse, seconds,
    outputReverse, output⟩
  change secondReverse = [] at reverseEq
  subst secondReverse
  simp only [FinTM2.step, TM2.step, machine, restoreSecondsCfg,
    scanFirstFieldCfg, emptyCfg, cfg, program, TM2.stepAux,
    unaryIsNone, unarySymbol, clear, update_tapes_secondReverse]
  rfl

end UnaryAlignedAddMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksTapes

/-! # Parsing steps for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open Turing

theorem step_scanLeft_left (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    machine.step (scanLeftCfg data) =
      some (pushRankReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, pushRankReverseCfg,
    inputCfg, emptyCfg, cfg, tapes, inputIsNone, inputIsLeft, inputSymbol]
  rfl

theorem step_pushRankReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushRankReverseCfg symbol data) =
      some (scanLeftCfg
        { data with rankReverse := symbol :: data.rankReverse }) := by
  simp [TM2.step, program, pushRankReverseCfg, scanLeftCfg,
    inputCfg, emptyCfg, cfg, tapes, leftSymbol, clear]
  rfl

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, scanRightCfg, emptyCfg, cfg,
    tapes, inputIsNone, inputIsLeft, inputIsSeparator, inputSymbol, clear]
  rfl

theorem step_scanRight_right (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanRightCfg data) =
      some (pushSizeReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, pushSizeReverseCfg,
    inputCfg, emptyCfg, cfg, tapes, inputIsNone, inputIsRight, inputSymbol]
  rfl

theorem step_pushSizeReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSizeReverseCfg symbol data) =
      some (scanRightCfg
        { data with sizeReverse := symbol :: data.sizeReverse }) := by
  simp [TM2.step, program, pushSizeReverseCfg, scanRightCfg,
    inputCfg, emptyCfg, cfg, tapes, rightSymbol, clear]
  rfl

theorem step_scanRight_nil (data : TapeData) (inputEq : data.input = []) :
    machine.step (scanRightCfg data) =
      some (restoreRanksCfg { data with input := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, restoreRanksCfg,
    emptyCfg, cfg, tapes, inputIsNone, inputSymbol, clear]
  rfl

theorem step_restoreRanks_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.rankReverse = symbol :: remaining) :
    machine.step (restoreRanksCfg data) =
      some (pushRankCfg symbol { data with rankReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change rankReverse = _ at reverseEq
  subst rankReverse
  simp [TM2.step, program, restoreRanksCfg, pushRankCfg,
    unaryCfg, emptyCfg, cfg, tapes, unaryIsNone, unarySymbol]
  rfl

theorem step_pushRank (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushRankCfg symbol data) =
      some (restoreRanksCfg { data with ranks := symbol :: data.ranks }) := by
  simp [TM2.step, program, pushRankCfg, restoreRanksCfg,
    unaryCfg, emptyCfg, cfg, tapes, storedUnary, clear]
  rfl

theorem step_restoreRanks_nil (data : TapeData)
    (reverseEq : data.rankReverse = []) :
    machine.step (restoreRanksCfg data) =
      some (restoreSizesCfg { data with rankReverse := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change rankReverse = [] at reverseEq
  subst rankReverse
  simp [TM2.step, program, restoreRanksCfg, restoreSizesCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]
  rfl

theorem step_restoreSizes_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.sizeReverse = symbol :: remaining) :
    machine.step (restoreSizesCfg data) =
      some (pushSizeCfg symbol { data with sizeReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizeReverse = _ at reverseEq
  subst sizeReverse
  simp [TM2.step, program, restoreSizesCfg, pushSizeCfg,
    unaryCfg, emptyCfg, cfg, tapes, unaryIsNone, unarySymbol]
  rfl

theorem step_pushSize (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushSizeCfg symbol data) =
      some (restoreSizesCfg { data with sizes := symbol :: data.sizes }) := by
  simp [TM2.step, program, pushSizeCfg, restoreSizesCfg,
    unaryCfg, emptyCfg, cfg, tapes, storedUnary, clear]
  rfl

theorem step_restoreSizes_nil (data : TapeData)
    (reverseEq : data.sizeReverse = []) :
    machine.step (restoreSizesCfg data) =
      some (scanRankCfg { data with sizeReverse := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizeReverse = [] at reverseEq
  subst sizeReverse
  simp [TM2.step, program, restoreSizesCfg, scanRankCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]
  rfl

end UnaryRotatedRanksMachine
end LeanTrominoes

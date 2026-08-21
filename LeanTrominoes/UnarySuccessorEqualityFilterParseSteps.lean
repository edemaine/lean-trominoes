/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterTapes

/-! # Parsing steps of the unary successor-equality filter -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open Turing

def scanLeftCfg (data : TapeData) := emptyCfg .scanLeft data
def pushRankReverseCfg (symbol : UnarySymbol) (data : TapeData) :=
  cfg .pushRankReverse (.input (some (.left symbol))) data
def scanRightCfg (data : TapeData) := emptyCfg .scanRight data
def pushSizeReverseCfg (symbol : UnarySymbol) (data : TapeData) :=
  cfg .pushSizeReverse (.input (some (.right symbol))) data
def restoreRanksCfg (data : TapeData) := emptyCfg .restoreRanks data
def pushRankCfg (symbol : UnarySymbol) (data : TapeData) :=
  cfg .pushRank (.unary (some symbol)) data
def restoreSizesCfg (data : TapeData) := emptyCfg .restoreSizes data
def pushSizeCfg (symbol : UnarySymbol) (data : TapeData) :=
  cfg .pushSize (.unary (some symbol)) data
def scanRankCfg (data : TapeData) := emptyCfg .scanRank data

theorem step_scanLeft_left (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    TM2.step program (scanLeftCfg data) =
      some (pushRankReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, pushRankReverseCfg,
    emptyCfg, cfg, tapes, inputIsNone, inputIsLeft, inputSymbol]

theorem step_pushRankReverse (data : TapeData) (symbol : UnarySymbol) :
    TM2.step program (pushRankReverseCfg symbol data) =
      some (scanLeftCfg
        { data with rankReverse := symbol :: data.rankReverse }) := by
  simp [TM2.step, program, pushRankReverseCfg, scanLeftCfg,
    emptyCfg, cfg, tapes, leftSymbol, clear]

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    TM2.step program (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, scanRightCfg, emptyCfg, cfg,
    tapes, inputIsNone, inputIsLeft, inputIsSeparator, inputSymbol, clear]

theorem step_scanRight_right (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    TM2.step program (scanRightCfg data) =
      some (pushSizeReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, pushSizeReverseCfg,
    emptyCfg, cfg, tapes, inputIsNone, inputIsRight, inputSymbol]

theorem step_pushSizeReverse (data : TapeData) (symbol : UnarySymbol) :
    TM2.step program (pushSizeReverseCfg symbol data) =
      some (scanRightCfg
        { data with sizeReverse := symbol :: data.sizeReverse }) := by
  simp [TM2.step, program, pushSizeReverseCfg, scanRightCfg,
    emptyCfg, cfg, tapes, rightSymbol, clear]

theorem step_scanRight_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanRightCfg data) =
      some (restoreRanksCfg { data with input := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, restoreRanksCfg,
    emptyCfg, cfg, tapes, inputIsNone, inputSymbol, clear]

theorem step_restoreRanks_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.rankReverse = symbol :: remaining) :
    TM2.step program (restoreRanksCfg data) =
      some (pushRankCfg symbol
        { data with rankReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change rankReverse = _ at reverseEq
  subst rankReverse
  simp [TM2.step, program, restoreRanksCfg, pushRankCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol]

theorem step_pushRank (data : TapeData) (symbol : UnarySymbol) :
    TM2.step program (pushRankCfg symbol data) =
      some (restoreRanksCfg { data with ranks := symbol :: data.ranks }) := by
  simp [TM2.step, program, pushRankCfg, restoreRanksCfg,
    emptyCfg, cfg, tapes, storedUnary, clear]

theorem step_restoreRanks_nil (data : TapeData)
    (reverseEq : data.rankReverse = []) :
    TM2.step program (restoreRanksCfg data) =
      some (restoreSizesCfg { data with rankReverse := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change rankReverse = [] at reverseEq
  subst rankReverse
  simp [TM2.step, program, restoreRanksCfg, restoreSizesCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]

theorem step_restoreSizes_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.sizeReverse = symbol :: remaining) :
    TM2.step program (restoreSizesCfg data) =
      some (pushSizeCfg symbol { data with sizeReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizeReverse = _ at reverseEq
  subst sizeReverse
  simp [TM2.step, program, restoreSizesCfg, pushSizeCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol]

theorem step_pushSize (data : TapeData) (symbol : UnarySymbol) :
    TM2.step program (pushSizeCfg symbol data) =
      some (restoreSizesCfg { data with sizes := symbol :: data.sizes }) := by
  simp [TM2.step, program, pushSizeCfg, restoreSizesCfg,
    emptyCfg, cfg, tapes, storedUnary, clear]

theorem step_restoreSizes_nil (data : TapeData)
    (reverseEq : data.sizeReverse = []) :
    TM2.step program (restoreSizesCfg data) =
      some (scanRankCfg { data with sizeReverse := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizeReverse = [] at reverseEq
  subst sizeReverse
  simp [TM2.step, program, restoreSizesCfg, scanRankCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes

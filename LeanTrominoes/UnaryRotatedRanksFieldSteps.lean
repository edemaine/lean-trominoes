/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksTapes

/-! # Field and output steps for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open Turing

theorem step_scanRank_nil (data : TapeData) (ranksEq : data.ranks = []) :
    machine.step (scanRankCfg data) =
      some (reverseOutputCfg { data with ranks := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change ranks = [] at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, reverseOutputCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]
  rfl

theorem step_scanRank_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .unit :: remaining) :
    machine.step (scanRankCfg data) =
      some (positiveRankRestCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, positiveRankRestCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_scanRank_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .delimiter :: remaining) :
    machine.step (scanRankCfg data) =
      some (zeroRankFirstSizeCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, zeroRankFirstSizeCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_positiveRankRest_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .unit :: remaining) :
    machine.step (positiveRankRestCfg data) =
      some (pushPositiveUnitCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, positiveRankRestCfg, pushPositiveUnitCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_positiveRankRest_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .delimiter :: remaining) :
    machine.step (positiveRankRestCfg data) =
      some (drainSizeCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, positiveRankRestCfg, drainSizeCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_pushPositiveUnit (data : TapeData) :
    machine.step (pushPositiveUnitCfg data) =
      some (positiveRankRestCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp [TM2.step, program, pushPositiveUnitCfg, positiveRankRestCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_zeroRankFirstSize_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    machine.step (zeroRankFirstSizeCfg data) =
      some (zeroRankRestSizeCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, zeroRankFirstSizeCfg, zeroRankRestSizeCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_zeroRankRestSize_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    machine.step (zeroRankRestSizeCfg data) =
      some (pushZeroUnitCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, zeroRankRestSizeCfg, pushZeroUnitCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_zeroRankRestSize_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .delimiter :: remaining) :
    machine.step (zeroRankRestSizeCfg data) =
      some (emitDelimiterCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, zeroRankRestSizeCfg, emitDelimiterCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_pushZeroUnit (data : TapeData) :
    machine.step (pushZeroUnitCfg data) =
      some (zeroRankRestSizeCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp [TM2.step, program, pushZeroUnitCfg, zeroRankRestSizeCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_drainSize_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    machine.step (drainSizeCfg data) =
      some (drainSizeCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, drainSizeCfg, emptyCfg, cfg, tapes,
    unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_drainSize_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .delimiter :: remaining) :
    machine.step (drainSizeCfg data) =
      some (emitDelimiterCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, drainSizeCfg, emitDelimiterCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]
  rfl

theorem step_emitDelimiter (data : TapeData) :
    machine.step (emitDelimiterCfg data) =
      some (scanRankCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  simp [TM2.step, program, emitDelimiterCfg, scanRankCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]
  rfl

theorem step_reverseOutput_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.outputReverse = symbol :: remaining) :
    machine.step (reverseOutputCfg data) =
      some (pushOutputCfg symbol { data with outputReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    outputReverse, output⟩
  change outputReverse = _ at reverseEq
  subst outputReverse
  cases symbol <;>
    simp [TM2.step, program, reverseOutputCfg, pushOutputCfg,
      unaryCfg, emptyCfg, cfg, tapes, unaryIsNone, unarySymbol] <;>
    rfl

theorem step_pushOutput (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushOutputCfg symbol data) =
      some (reverseOutputCfg
        { data with output := symbol :: data.output }) := by
  cases symbol <;>
    simp [TM2.step, program, pushOutputCfg, reverseOutputCfg,
      unaryCfg, emptyCfg, cfg, tapes, storedUnary, clear] <;>
    rfl

end UnaryRotatedRanksMachine
end LeanTrominoes

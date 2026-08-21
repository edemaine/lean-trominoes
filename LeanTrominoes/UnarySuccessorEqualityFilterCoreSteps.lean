/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterParseExecution

/-! # Field-filtering steps for unary successor equality -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open Turing

def matchSizeUnitCfg (data : TapeData) := emptyCfg .matchSizeUnit data
def pushMatchedUnitCfg (data : TapeData) := emptyCfg .pushMatchedUnit data
def checkExtraSizeCfg (data : TapeData) := emptyCfg .checkExtraSize data
def pushExtraUnitCfg (data : TapeData) := emptyCfg .pushExtraUnit data
def checkSizeDelimiterCfg (data : TapeData) := emptyCfg .checkSizeDelimiter data
def rejectDrainRankCfg (data : TapeData) := emptyCfg .rejectDrainRank data
def rejectDrainSizeCfg (data : TapeData) := emptyCfg .rejectDrainSize data
def clearCandidateCfg (data : TapeData) := emptyCfg .clearCandidate data
def drainCandidateCfg (data : TapeData) := emptyCfg .drainCandidate data
def pushOutputUnitCfg (data : TapeData) := emptyCfg .pushOutputUnit data
def emitDelimiterCfg (data : TapeData) := emptyCfg .emitDelimiter data
def reverseOutputCfg (data : TapeData) := emptyCfg .reverseOutput data
def pushOutputCfg (symbol : UnarySymbol) (data : TapeData) :=
  cfg .pushOutput (.unary (some symbol)) data

theorem step_scanRank_unit (data : TapeData) (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .unit :: remaining) :
    TM2.step program (scanRankCfg data) =
      some (matchSizeUnitCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, matchSizeUnitCfg, emptyCfg,
    cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_matchSizeUnit_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    TM2.step program (matchSizeUnitCfg data) =
      some (pushMatchedUnitCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, matchSizeUnitCfg, pushMatchedUnitCfg,
    emptyCfg, cfg, tapes, unaryIsUnit, clear]

theorem step_pushMatchedUnit (data : TapeData) :
    TM2.step program (pushMatchedUnitCfg data) =
      some (scanRankCfg
        { data with candidate := () :: data.candidate }) := by
  simp [TM2.step, program, pushMatchedUnitCfg, scanRankCfg,
    emptyCfg, cfg, tapes]

theorem step_scanRank_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .delimiter :: remaining) :
    TM2.step program (scanRankCfg data) =
      some (checkExtraSizeCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, checkExtraSizeCfg, emptyCfg,
    cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_checkExtraSize_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    TM2.step program (checkExtraSizeCfg data) =
      some (pushExtraUnitCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, checkExtraSizeCfg, pushExtraUnitCfg,
    emptyCfg, cfg, tapes, unaryIsUnit, clear]

theorem step_pushExtraUnit (data : TapeData) :
    TM2.step program (pushExtraUnitCfg data) =
      some (checkSizeDelimiterCfg
        { data with candidate := () :: data.candidate }) := by
  simp [TM2.step, program, pushExtraUnitCfg, checkSizeDelimiterCfg,
    emptyCfg, cfg, tapes]

theorem step_checkSizeDelimiter_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .delimiter :: remaining) :
    TM2.step program (checkSizeDelimiterCfg data) =
      some (drainCandidateCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, checkSizeDelimiterCfg, drainCandidateCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_checkSizeDelimiter_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    TM2.step program (checkSizeDelimiterCfg data) =
      some (rejectDrainSizeCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, checkSizeDelimiterCfg, rejectDrainSizeCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_rejectDrainRank_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .unit :: remaining) :
    TM2.step program (rejectDrainRankCfg data) =
      some (rejectDrainRankCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, rejectDrainRankCfg, emptyCfg, cfg, tapes,
    unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_rejectDrainRank_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (ranksEq : data.ranks = .delimiter :: remaining) :
    TM2.step program (rejectDrainRankCfg data) =
      some (clearCandidateCfg { data with ranks := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = _ at ranksEq
  subst ranks
  simp [TM2.step, program, rejectDrainRankCfg, clearCandidateCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_rejectDrainRank_nil (data : TapeData)
    (ranksEq : data.ranks = []) :
    TM2.step program (rejectDrainRankCfg data) =
      some (clearCandidateCfg { data with ranks := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = [] at ranksEq
  subst ranks
  simp [TM2.step, program, rejectDrainRankCfg, clearCandidateCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol, clear]

theorem step_rejectDrainSize_unit (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .unit :: remaining) :
    TM2.step program (rejectDrainSizeCfg data) =
      some (rejectDrainSizeCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, rejectDrainSizeCfg, emptyCfg, cfg, tapes,
    unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_rejectDrainSize_delimiter (data : TapeData)
    (remaining : List UnarySymbol)
    (sizesEq : data.sizes = .delimiter :: remaining) :
    TM2.step program (rejectDrainSizeCfg data) =
      some (clearCandidateCfg { data with sizes := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change sizes = _ at sizesEq
  subst sizes
  simp [TM2.step, program, rejectDrainSizeCfg, clearCandidateCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unaryIsUnit, unarySymbol, clear]

theorem step_clearCandidate_cons (data : TapeData) (remaining : List Unit)
    (candidateEq : data.candidate = () :: remaining) :
    TM2.step program (clearCandidateCfg data) =
      some (clearCandidateCfg { data with candidate := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change candidate = _ at candidateEq
  subst candidate
  simp [TM2.step, program, clearCandidateCfg, emptyCfg, cfg, tapes,
    candidateIsNone, clear]

theorem step_clearCandidate_nil (data : TapeData)
    (candidateEq : data.candidate = []) :
    TM2.step program (clearCandidateCfg data) =
      some (emitDelimiterCfg { data with candidate := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change candidate = [] at candidateEq
  subst candidate
  simp [TM2.step, program, clearCandidateCfg, emitDelimiterCfg,
    emptyCfg, cfg, tapes, candidateIsNone, clear]

theorem step_drainCandidate_cons (data : TapeData) (remaining : List Unit)
    (candidateEq : data.candidate = () :: remaining) :
    TM2.step program (drainCandidateCfg data) =
      some (pushOutputUnitCfg { data with candidate := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change candidate = _ at candidateEq
  subst candidate
  simp [TM2.step, program, drainCandidateCfg, pushOutputUnitCfg,
    emptyCfg, cfg, tapes, candidateIsNone, clear]

theorem step_drainCandidate_nil (data : TapeData)
    (candidateEq : data.candidate = []) :
    TM2.step program (drainCandidateCfg data) =
      some (emitDelimiterCfg { data with candidate := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change candidate = [] at candidateEq
  subst candidate
  simp [TM2.step, program, drainCandidateCfg, emitDelimiterCfg,
    emptyCfg, cfg, tapes, candidateIsNone, clear]

theorem step_pushOutputUnit (data : TapeData) :
    TM2.step program (pushOutputUnitCfg data) =
      some (drainCandidateCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp [TM2.step, program, pushOutputUnitCfg, drainCandidateCfg,
    emptyCfg, cfg, tapes, clear]

theorem step_emitDelimiter (data : TapeData) :
    TM2.step program (emitDelimiterCfg data) =
      some (scanRankCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  simp [TM2.step, program, emitDelimiterCfg, scanRankCfg,
    emptyCfg, cfg, tapes, clear]

theorem step_scanRank_nil (data : TapeData) (ranksEq : data.ranks = []) :
    TM2.step program (scanRankCfg data) =
      some (reverseOutputCfg { data with ranks := [] }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change ranks = [] at ranksEq
  subst ranks
  simp [TM2.step, program, scanRankCfg, reverseOutputCfg, emptyCfg,
    cfg, tapes, unaryIsNone, unarySymbol, clear]

theorem step_reverseOutput_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.outputReverse = symbol :: remaining) :
    TM2.step program (reverseOutputCfg data) =
      some (pushOutputCfg symbol
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change outputReverse = _ at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, pushOutputCfg,
    emptyCfg, cfg, tapes, unaryIsNone, unarySymbol]

theorem step_pushOutput (data : TapeData) (symbol : UnarySymbol) :
    TM2.step program (pushOutputCfg symbol data) =
      some (reverseOutputCfg
        { data with output := symbol :: data.output }) := by
  simp [TM2.step, program, pushOutputCfg, reverseOutputCfg,
    emptyCfg, cfg, tapes, storedUnary, clear]

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some ⟨none, .empty, tapes { data with outputReverse := [] }⟩ := by
  rcases data with ⟨input, rankReverse, ranks, sizeReverse, sizes,
    candidate, outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, emptyCfg, cfg, tapes,
    unaryIsNone, unarySymbol, clear]

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes

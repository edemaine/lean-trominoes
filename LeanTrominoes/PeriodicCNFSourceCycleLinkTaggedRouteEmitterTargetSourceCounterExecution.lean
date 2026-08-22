/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Target-record source-index field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetSourceCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetSourceLiteral tag data)
      (some (copyCounterCfg .targetTargetIndex tag
        (afterTargetSourceCounters data)))
      (targetSourceCountersTime data) := by
  have literal := counter_evalsInTime .targetSourceLiteral tag data
    data.literalCount rfl scratchEq
  have literal' : EvalsToInTime machine.step
      (copyCounterCfg .targetSourceLiteral tag data)
      (some (copyCounterCfg .targetSourceClause tag
        (afterTargetSourceLiteralCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterTargetSourceLiteralCounter] using literal
  have clauses := counter_evalsInTime .targetSourceClause tag
    (afterTargetSourceLiteralCounter data) data.clauseCount rfl rfl
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .targetSourceClause tag
        (afterTargetSourceLiteralCounter data))
      (some (copyCounterCfg .targetSourceIndex tag
        (afterTargetSourceClauseCounter data)))
      (counterTime data.clauseCount) := by
    simpa only [afterCounterCfg,
      afterTargetSourceClauseCounter] using clauses
  have index := counter_evalsInTime .targetSourceIndex tag
    (afterTargetSourceClauseCounter data) data.linkIndex rfl rfl
  have index' : EvalsToInTime machine.step
      (copyCounterCfg .targetSourceIndex tag
        (afterTargetSourceClauseCounter data))
      (some (copyCounterCfg .targetTargetIndex tag
        (afterTargetSourceCounters data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg, afterTargetSourceCounters,
      closeOutputField, afterTargetSourceClauseCounter] using index
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.clauseCount)
    _ _ _ literal' clauses'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.clauseCount + counterTime data.literalCount)
    (counterTime data.linkIndex) _ _ _ firstTwo index'
  simpa only [targetSourceCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

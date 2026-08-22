/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Target-record vertex field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetVertexCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetVertexClause tag data)
      (some (copyCounterCfg .targetEdgeLiteralFirst tag
        (afterTargetVertexCounters data)))
      (targetVertexCountersTime data) := by
  have clauses := counter_evalsInTime .targetVertexClause tag data
    data.clauseCount rfl scratchEq
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .targetVertexClause tag data)
      (some (copyCounterCfg .targetVertexLiteralFirst tag
        (afterTargetVertexClauseCounter data)))
      (counterTime data.clauseCount) := by
    simpa only [afterCounterCfg, afterTargetVertexClauseCounter] using clauses
  have first := counter_evalsInTime .targetVertexLiteralFirst tag
    (afterTargetVertexClauseCounter data) data.literalCount rfl rfl
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .targetVertexLiteralFirst tag
        (afterTargetVertexClauseCounter data))
      (some (copyCounterCfg .targetVertexLiteralSecond tag
        (afterTargetVertexLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterTargetVertexLiteralFirstCounter] using first
  have second := counter_evalsInTime .targetVertexLiteralSecond tag
    (afterTargetVertexLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .targetVertexLiteralSecond tag
        (afterTargetVertexLiteralFirstCounter data))
      (some (copyCounterCfg .targetEdgeLiteralFirst tag
        (afterTargetVertexCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterTargetVertexCounters,
      closeOutputField, afterTargetVertexLiteralFirstCounter] using second
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.clauseCount) (counterTime data.literalCount)
    _ _ _ clauses' first'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.clauseCount)
    (counterTime data.literalCount) _ _ _ firstTwo second'
  simpa only [targetVertexCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

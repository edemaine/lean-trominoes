/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Source-record vertex field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourceVertexCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceVertexClause tag data)
      (some (copyCounterCfg .sourceEdgeLiteralFirst tag
        (afterSourceVertexCounters data)))
      (sourceVertexCountersTime data) := by
  have clauses := counter_evalsInTime .sourceVertexClause tag data
    data.clauseCount rfl scratchEq
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .sourceVertexClause tag data)
      (some (copyCounterCfg .sourceVertexLiteralFirst tag
        (afterSourceVertexClauseCounter data)))
      (counterTime data.clauseCount) := by
    simpa only [afterCounterCfg, afterSourceVertexClauseCounter] using clauses
  have first := counter_evalsInTime .sourceVertexLiteralFirst tag
    (afterSourceVertexClauseCounter data) data.literalCount rfl rfl
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .sourceVertexLiteralFirst tag
        (afterSourceVertexClauseCounter data))
      (some (copyCounterCfg .sourceVertexLiteralSecond tag
        (afterSourceVertexLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterSourceVertexLiteralFirstCounter] using first
  have second := counter_evalsInTime .sourceVertexLiteralSecond tag
    (afterSourceVertexLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .sourceVertexLiteralSecond tag
        (afterSourceVertexLiteralFirstCounter data))
      (some (copyCounterCfg .sourceEdgeLiteralFirst tag
        (afterSourceVertexCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterSourceVertexCounters,
      closeOutputField, afterSourceVertexLiteralFirstCounter] using second
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.clauseCount) (counterTime data.literalCount)
    _ _ _ clauses' first'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.clauseCount)
    (counterTime data.literalCount) _ _ _ firstTwo second'
  simpa only [sourceVertexCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

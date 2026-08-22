/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordCounterData

/-! # Vertex-count field execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def vertexCounters_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .vertexClauses cursor data)
      (some (copyCounterCfg .edgeLiteralsFirst cursor
        (afterVertexCounters data)))
      (vertexCountersTime data) := by
  have clauses := counter_evalsInTime .vertexClauses cursor data
    data.clauseCount rfl scratchEq
  have clauses' : EvalsToInTime machine.step
      (copyCounterCfg .vertexClauses cursor data)
      (some (copyCounterCfg .vertexLiteralsFirst cursor
        (afterVertexClauseCounter data)))
      (counterTime data.clauseCount) := by
    simpa only [afterCounterCfg, afterVertexClauseCounter] using clauses
  have first := counter_evalsInTime .vertexLiteralsFirst cursor
    (afterVertexClauseCounter data) data.literalCount rfl rfl
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .vertexLiteralsFirst cursor
        (afterVertexClauseCounter data))
      (some (copyCounterCfg .vertexLiteralsSecond cursor
        (afterVertexLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterVertexLiteralFirstCounter] using first
  have second := counter_evalsInTime .vertexLiteralsSecond cursor
    (afterVertexLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .vertexLiteralsSecond cursor
        (afterVertexLiteralFirstCounter data))
      (some (copyCounterCfg .edgeLiteralsFirst cursor
        (afterVertexCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterVertexCounters, closeOutputField,
      afterVertexLiteralFirstCounter] using second
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.clauseCount) (counterTime data.literalCount)
    (copyCounterCfg .vertexClauses cursor data)
    (copyCounterCfg .vertexLiteralsFirst cursor
      (afterVertexClauseCounter data))
    (some (copyCounterCfg .vertexLiteralsSecond cursor
      (afterVertexLiteralFirstCounter data)))
    clauses' first'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.clauseCount)
    (counterTime data.literalCount)
    (copyCounterCfg .vertexClauses cursor data)
    (copyCounterCfg .vertexLiteralsSecond cursor
      (afterVertexLiteralFirstCounter data))
    (some (copyCounterCfg .edgeLiteralsFirst cursor
      (afterVertexCounters data)))
    firstTwo second'
  simpa only [vertexCountersTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

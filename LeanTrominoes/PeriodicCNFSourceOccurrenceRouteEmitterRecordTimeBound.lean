/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecutionData

/-! # Linear bound for one source-occurrence route record -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def recordSize (data : TapeData) (targetCount : Nat) : Nat :=
  data.clauseCount.length + data.literalCount.length +
    data.clauseIndex.length + data.edgeIndex.length + targetCount + 1

theorem recordTime_le (data : TapeData) (targetCount : Nat) :
    recordTime data targetCount ≤ 21 * recordSize data targetCount := by
  simp only [recordTime, recordSuffixTime, recordCountersTime,
    sourceCountersTime, edgeCountersTime, vertexCountersTime,
    counterTime, beginRecordData, afterEdgeIndexCounter,
    afterCounterData, closeOutputField, afterEdgeCounters,
    afterEdgeLiteralSecondCounter, afterEdgeLiteralFirstCounter,
    afterVertexCounters, afterVertexLiteralFirstCounter,
    afterVertexClauseCounter, recordSize]
  omega

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

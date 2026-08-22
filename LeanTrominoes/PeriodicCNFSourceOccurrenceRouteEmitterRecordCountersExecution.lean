/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterVertexCounterExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterEdgeCounterExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterEdgeIndexCounterExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSourceCounterExecution

/-! # Complete record-counter execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def afterRecordCounters (data : TapeData) : TapeData :=
  afterSourceCounters
    (afterEdgeIndexCounter (afterEdgeCounters (afterVertexCounters data)))

@[simp] theorem afterRecordCounters_targets (data : TapeData) :
    (afterRecordCounters data).targets = data.targets := by
  simp only [afterRecordCounters, afterSourceCounters_targets,
    afterEdgeIndexCounter_targets, afterEdgeCounters_targets,
    afterVertexCounters_targets]

def recordCountersTime (data : TapeData) : Nat :=
  sourceCountersTime
      (afterEdgeIndexCounter (afterEdgeCounters (afterVertexCounters data))) +
    (counterTime (afterEdgeCounters (afterVertexCounters data)).edgeIndex +
      (edgeCountersTime (afterVertexCounters data) +
        vertexCountersTime data))

noncomputable def recordCounters_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .vertexClauses cursor data)
      (some (scanTargetCfg cursor (afterRecordCounters data)))
      (recordCountersTime data) := by
  have vertex := vertexCounters_evalsInTime cursor data scratchEq
  have edge := edgeCounters_evalsInTime cursor
    (afterVertexCounters data) rfl
  have throughEdge := EvalsToInTime.trans machine.step
    (vertexCountersTime data)
    (edgeCountersTime (afterVertexCounters data))
    (copyCounterCfg .vertexClauses cursor data)
    (copyCounterCfg .edgeLiteralsFirst cursor (afterVertexCounters data))
    (some (copyCounterCfg .edgeIndex cursor
      (afterEdgeCounters (afterVertexCounters data))))
    vertex edge
  have edgeIndex := edgeIndexCounter_evalsInTime cursor
    (afterEdgeCounters (afterVertexCounters data)) rfl
  have throughEdgeIndex := EvalsToInTime.trans machine.step
    (edgeCountersTime (afterVertexCounters data) + vertexCountersTime data)
    (counterTime (afterEdgeCounters (afterVertexCounters data)).edgeIndex)
    (copyCounterCfg .vertexClauses cursor data)
    (copyCounterCfg .edgeIndex cursor
      (afterEdgeCounters (afterVertexCounters data)))
    (some (copyCounterCfg .sourceLiterals cursor
      (afterEdgeIndexCounter
        (afterEdgeCounters (afterVertexCounters data)))))
    throughEdge edgeIndex
  have source := sourceCounters_evalsInTime cursor
    (afterEdgeIndexCounter (afterEdgeCounters (afterVertexCounters data))) rfl
  have whole := EvalsToInTime.trans machine.step
    (counterTime (afterEdgeCounters (afterVertexCounters data)).edgeIndex +
      (edgeCountersTime (afterVertexCounters data) +
        vertexCountersTime data))
    (sourceCountersTime
      (afterEdgeIndexCounter (afterEdgeCounters (afterVertexCounters data))))
    (copyCounterCfg .vertexClauses cursor data)
    (copyCounterCfg .sourceLiterals cursor
      (afterEdgeIndexCounter
        (afterEdgeCounters (afterVertexCounters data))))
    (some (scanTargetCfg cursor (afterRecordCounters data)))
    throughEdgeIndex source
  simpa only [recordCountersTime, afterRecordCounters] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

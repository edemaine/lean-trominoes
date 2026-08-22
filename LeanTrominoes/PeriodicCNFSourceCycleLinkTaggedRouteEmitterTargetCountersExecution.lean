/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetEdgeCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetEdgeIndexCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetIndexCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetSourceCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetVertexCounterExecution

/-! # Complete target-record counter execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def afterTargetCounters (data : TapeData) : TapeData :=
  afterTargetTargetIndexCounter
    (afterTargetSourceCounters
      (afterTargetEdgeIndexCounters
        (afterTargetEdgeCounters (afterTargetVertexCounters data))))

def targetCountersTime (data : TapeData) : Nat :=
  counterTime
      (afterTargetSourceCounters
        (afterTargetEdgeIndexCounters
          (afterTargetEdgeCounters
            (afterTargetVertexCounters data)))).linkIndex +
    (targetSourceCountersTime
        (afterTargetEdgeIndexCounters
          (afterTargetEdgeCounters (afterTargetVertexCounters data))) +
      (targetEdgeIndexCountersTime
          (afterTargetEdgeCounters (afterTargetVertexCounters data)) +
        (targetEdgeCountersTime (afterTargetVertexCounters data) +
          targetVertexCountersTime data)))

noncomputable def targetCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetVertexClause tag data)
      (some (finishTargetRecordCfg tag (afterTargetCounters data)))
      (targetCountersTime data) := by
  have vertex := targetVertexCounters_evalsInTime tag data scratchEq
  have edge := targetEdgeCounters_evalsInTime tag
    (afterTargetVertexCounters data) rfl
  have throughEdge := EvalsToInTime.trans machine.step
    (targetVertexCountersTime data)
    (targetEdgeCountersTime (afterTargetVertexCounters data))
    _ _ _ vertex edge
  have edgeIndex := targetEdgeIndexCounters_evalsInTime tag
    (afterTargetEdgeCounters (afterTargetVertexCounters data)) rfl
  have throughEdgeIndex := EvalsToInTime.trans machine.step
    (targetEdgeCountersTime (afterTargetVertexCounters data) +
      targetVertexCountersTime data)
    (targetEdgeIndexCountersTime
      (afterTargetEdgeCounters (afterTargetVertexCounters data)))
    _ _ _ throughEdge edgeIndex
  have source := targetSourceCounters_evalsInTime tag
    (afterTargetEdgeIndexCounters
      (afterTargetEdgeCounters (afterTargetVertexCounters data))) rfl
  have throughSource := EvalsToInTime.trans machine.step
    (targetEdgeIndexCountersTime
        (afterTargetEdgeCounters (afterTargetVertexCounters data)) +
      (targetEdgeCountersTime (afterTargetVertexCounters data) +
        targetVertexCountersTime data))
    (targetSourceCountersTime
      (afterTargetEdgeIndexCounters
        (afterTargetEdgeCounters (afterTargetVertexCounters data))))
    _ _ _ throughEdgeIndex source
  have target := targetIndexCounter_evalsInTime tag
    (afterTargetSourceCounters
      (afterTargetEdgeIndexCounters
        (afterTargetEdgeCounters (afterTargetVertexCounters data)))) rfl
  have whole := EvalsToInTime.trans machine.step
    (targetSourceCountersTime
        (afterTargetEdgeIndexCounters
          (afterTargetEdgeCounters (afterTargetVertexCounters data))) +
      (targetEdgeIndexCountersTime
          (afterTargetEdgeCounters (afterTargetVertexCounters data)) +
        (targetEdgeCountersTime (afterTargetVertexCounters data) +
          targetVertexCountersTime data)))
    (counterTime
      (afterTargetSourceCounters
        (afterTargetEdgeIndexCounters
          (afterTargetEdgeCounters
            (afterTargetVertexCounters data)))).linkIndex)
    _ _ _ throughSource target
  simpa only [targetCountersTime, afterTargetCounters] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

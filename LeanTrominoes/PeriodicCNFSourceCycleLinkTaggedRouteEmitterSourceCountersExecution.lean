/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceEdgeCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceEdgeIndexCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceSourceCounterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceVertexCounterExecution

/-! # Complete source-record counter execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def afterSourceCounters (data : TapeData) : TapeData :=
  afterSourceSourceCounters
    (afterSourceEdgeIndexCounters
      (afterSourceEdgeCounters (afterSourceVertexCounters data)))

def sourceCountersTime (data : TapeData) : Nat :=
  sourceSourceCountersTime
      (afterSourceEdgeIndexCounters
        (afterSourceEdgeCounters (afterSourceVertexCounters data))) +
    (sourceEdgeIndexCountersTime
        (afterSourceEdgeCounters (afterSourceVertexCounters data)) +
      (sourceEdgeCountersTime (afterSourceVertexCounters data) +
        sourceVertexCountersTime data))

noncomputable def sourceCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceVertexClause tag data)
      (some (scanTargetCfg tag (afterSourceCounters data)))
      (sourceCountersTime data) := by
  have vertex := sourceVertexCounters_evalsInTime tag data scratchEq
  have edge := sourceEdgeCounters_evalsInTime tag
    (afterSourceVertexCounters data) rfl
  have throughEdge := EvalsToInTime.trans machine.step
    (sourceVertexCountersTime data)
    (sourceEdgeCountersTime (afterSourceVertexCounters data))
    _ _ _ vertex edge
  have edgeIndex := sourceEdgeIndexCounters_evalsInTime tag
    (afterSourceEdgeCounters (afterSourceVertexCounters data)) rfl
  have throughEdgeIndex := EvalsToInTime.trans machine.step
    (sourceEdgeCountersTime (afterSourceVertexCounters data) +
      sourceVertexCountersTime data)
    (sourceEdgeIndexCountersTime
      (afterSourceEdgeCounters (afterSourceVertexCounters data)))
    _ _ _ throughEdge edgeIndex
  have source := sourceSourceCounters_evalsInTime tag
    (afterSourceEdgeIndexCounters
      (afterSourceEdgeCounters (afterSourceVertexCounters data))) rfl
  have whole := EvalsToInTime.trans machine.step
    (sourceEdgeIndexCountersTime
        (afterSourceEdgeCounters (afterSourceVertexCounters data)) +
      (sourceEdgeCountersTime (afterSourceVertexCounters data) +
        sourceVertexCountersTime data))
    (sourceSourceCountersTime
      (afterSourceEdgeIndexCounters
        (afterSourceEdgeCounters (afterSourceVertexCounters data))))
    _ _ _ throughEdgeIndex source
  simpa only [sourceCountersTime, afterSourceCounters] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

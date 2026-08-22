/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Source-record edge-index field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourceEdgeIndexCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeIndexLiteral tag data)
      (some (copyCounterCfg .sourceSourceLiteral tag
        (afterSourceEdgeIndexCounters data)))
      (sourceEdgeIndexCountersTime data) := by
  have literal := counter_evalsInTime .sourceEdgeIndexLiteral tag data
    data.literalCount rfl scratchEq
  have literal' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeIndexLiteral tag data)
      (some (copyCounterCfg .sourceEdgeIndexFirst tag
        (afterSourceEdgeIndexLiteralCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterSourceEdgeIndexLiteralCounter] using literal
  have first := counter_evalsInTime .sourceEdgeIndexFirst tag
    (afterSourceEdgeIndexLiteralCounter data) data.linkIndex rfl rfl
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeIndexFirst tag
        (afterSourceEdgeIndexLiteralCounter data))
      (some (copyCounterCfg .sourceEdgeIndexSecond tag
        (afterSourceEdgeIndexFirstCounter data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg,
      afterSourceEdgeIndexFirstCounter] using first
  have second := counter_evalsInTime .sourceEdgeIndexSecond tag
    (afterSourceEdgeIndexFirstCounter data) data.linkIndex rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeIndexSecond tag
        (afterSourceEdgeIndexFirstCounter data))
      (some (copyCounterCfg .sourceSourceLiteral tag
        (afterSourceEdgeIndexCounters data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg, afterSourceEdgeIndexCounters,
      closeOutputField, afterSourceEdgeIndexFirstCounter] using second
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.linkIndex)
    _ _ _ literal' first'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.linkIndex + counterTime data.literalCount)
    (counterTime data.linkIndex) _ _ _ firstTwo second'
  simpa only [sourceEdgeIndexCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

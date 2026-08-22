/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Target-record edge-index field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetEdgeIndexCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeIndexLiteral tag data)
      (some (copyCounterCfg .targetSourceLiteral tag
        (afterTargetEdgeIndexCounters data)))
      (targetEdgeIndexCountersTime data) := by
  have literal := counter_evalsInTime .targetEdgeIndexLiteral tag data
    data.literalCount rfl scratchEq
  have literal' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeIndexLiteral tag data)
      (some (copyCounterCfg .targetEdgeIndexFirst tag
        (afterTargetEdgeIndexLiteralCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterTargetEdgeIndexLiteralCounter] using literal
  have first := counter_evalsInTime .targetEdgeIndexFirst tag
    (afterTargetEdgeIndexLiteralCounter data) data.linkIndex rfl rfl
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeIndexFirst tag
        (afterTargetEdgeIndexLiteralCounter data))
      (some (copyCounterCfg .targetEdgeIndexSecond tag
        (afterTargetEdgeIndexFirstCounter data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg,
      afterTargetEdgeIndexFirstCounter] using first
  have second := counter_evalsInTime .targetEdgeIndexSecond tag
    (afterTargetEdgeIndexFirstCounter data) data.linkIndex rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeIndexSecond tag
        (afterTargetEdgeIndexFirstCounter data))
      (some (copyCounterCfg .targetSourceLiteral tag
        (afterTargetEdgeIndexCounters data)))
      (counterTime data.linkIndex) := by
    simpa only [afterCounterCfg, afterTargetEdgeIndexCounters,
      addOutputUnitAndClose, afterTargetEdgeIndexFirstCounter] using second
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.linkIndex)
    _ _ _ literal' first'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.linkIndex + counterTime data.literalCount)
    (counterTime data.linkIndex) _ _ _ firstTwo second'
  simpa only [targetEdgeIndexCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Target-record edge field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetEdgeCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeLiteralFirst tag data)
      (some (copyCounterCfg .targetEdgeIndexLiteral tag
        (afterTargetEdgeCounters data)))
      (targetEdgeCountersTime data) := by
  have first := counter_evalsInTime .targetEdgeLiteralFirst tag data
    data.literalCount rfl scratchEq
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeLiteralFirst tag data)
      (some (copyCounterCfg .targetEdgeLiteralSecond tag
        (afterTargetEdgeLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterTargetEdgeLiteralFirstCounter] using first
  have second := counter_evalsInTime .targetEdgeLiteralSecond tag
    (afterTargetEdgeLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeLiteralSecond tag
        (afterTargetEdgeLiteralFirstCounter data))
      (some (copyCounterCfg .targetEdgeLiteralThird tag
        (afterTargetEdgeLiteralSecondCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterTargetEdgeLiteralSecondCounter] using second
  have third := counter_evalsInTime .targetEdgeLiteralThird tag
    (afterTargetEdgeLiteralSecondCounter data) data.literalCount rfl rfl
  have third' : EvalsToInTime machine.step
      (copyCounterCfg .targetEdgeLiteralThird tag
        (afterTargetEdgeLiteralSecondCounter data))
      (some (copyCounterCfg .targetEdgeIndexLiteral tag
        (afterTargetEdgeCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterTargetEdgeCounters,
      closeOutputField, afterTargetEdgeLiteralSecondCounter] using third
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.literalCount)
    _ _ _ first' second'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.literalCount)
    (counterTime data.literalCount) _ _ _ firstTwo third'
  simpa only [targetEdgeCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

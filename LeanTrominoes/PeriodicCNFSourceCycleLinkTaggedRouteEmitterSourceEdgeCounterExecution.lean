/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Source-record edge field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourceEdgeCounters_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeLiteralFirst tag data)
      (some (copyCounterCfg .sourceEdgeIndexLiteral tag
        (afterSourceEdgeCounters data)))
      (sourceEdgeCountersTime data) := by
  have first := counter_evalsInTime .sourceEdgeLiteralFirst tag data
    data.literalCount rfl scratchEq
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeLiteralFirst tag data)
      (some (copyCounterCfg .sourceEdgeLiteralSecond tag
        (afterSourceEdgeLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterSourceEdgeLiteralFirstCounter] using first
  have second := counter_evalsInTime .sourceEdgeLiteralSecond tag
    (afterSourceEdgeLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeLiteralSecond tag
        (afterSourceEdgeLiteralFirstCounter data))
      (some (copyCounterCfg .sourceEdgeLiteralThird tag
        (afterSourceEdgeLiteralSecondCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg,
      afterSourceEdgeLiteralSecondCounter] using second
  have third := counter_evalsInTime .sourceEdgeLiteralThird tag
    (afterSourceEdgeLiteralSecondCounter data) data.literalCount rfl rfl
  have third' : EvalsToInTime machine.step
      (copyCounterCfg .sourceEdgeLiteralThird tag
        (afterSourceEdgeLiteralSecondCounter data))
      (some (copyCounterCfg .sourceEdgeIndexLiteral tag
        (afterSourceEdgeCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterSourceEdgeCounters,
      closeOutputField, afterSourceEdgeLiteralSecondCounter] using third
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.literalCount)
    _ _ _ first' second'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.literalCount)
    (counterTime data.literalCount) _ _ _ firstTwo third'
  simpa only [sourceEdgeCountersTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

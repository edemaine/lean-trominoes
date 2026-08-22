/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordCounterData

/-! # Edge-count field execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def edgeCounters_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .edgeLiteralsFirst cursor data)
      (some (copyCounterCfg .edgeIndex cursor (afterEdgeCounters data)))
      (edgeCountersTime data) := by
  have first := counter_evalsInTime .edgeLiteralsFirst cursor data
    data.literalCount rfl scratchEq
  have first' : EvalsToInTime machine.step
      (copyCounterCfg .edgeLiteralsFirst cursor data)
      (some (copyCounterCfg .edgeLiteralsSecond cursor
        (afterEdgeLiteralFirstCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterEdgeLiteralFirstCounter] using first
  have second := counter_evalsInTime .edgeLiteralsSecond cursor
    (afterEdgeLiteralFirstCounter data) data.literalCount rfl rfl
  have second' : EvalsToInTime machine.step
      (copyCounterCfg .edgeLiteralsSecond cursor
        (afterEdgeLiteralFirstCounter data))
      (some (copyCounterCfg .edgeLiteralsThird cursor
        (afterEdgeLiteralSecondCounter data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterEdgeLiteralSecondCounter] using second
  have third := counter_evalsInTime .edgeLiteralsThird cursor
    (afterEdgeLiteralSecondCounter data) data.literalCount rfl rfl
  have third' : EvalsToInTime machine.step
      (copyCounterCfg .edgeLiteralsThird cursor
        (afterEdgeLiteralSecondCounter data))
      (some (copyCounterCfg .edgeIndex cursor (afterEdgeCounters data)))
      (counterTime data.literalCount) := by
    simpa only [afterCounterCfg, afterEdgeCounters, closeOutputField,
      afterEdgeLiteralSecondCounter] using third
  have firstTwo := EvalsToInTime.trans machine.step
    (counterTime data.literalCount) (counterTime data.literalCount)
    (copyCounterCfg .edgeLiteralsFirst cursor data)
    (copyCounterCfg .edgeLiteralsSecond cursor
      (afterEdgeLiteralFirstCounter data))
    (some (copyCounterCfg .edgeLiteralsThird cursor
      (afterEdgeLiteralSecondCounter data)))
    first' second'
  have whole := EvalsToInTime.trans machine.step
    (counterTime data.literalCount + counterTime data.literalCount)
    (counterTime data.literalCount)
    (copyCounterCfg .edgeLiteralsFirst cursor data)
    (copyCounterCfg .edgeLiteralsThird cursor
      (afterEdgeLiteralSecondCounter data))
    (some (copyCounterCfg .edgeIndex cursor (afterEdgeCounters data)))
    firstTwo third'
  simpa only [edgeCountersTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

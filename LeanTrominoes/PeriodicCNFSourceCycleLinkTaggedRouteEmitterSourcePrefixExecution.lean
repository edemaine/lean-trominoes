/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkSteps
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData

/-! # Source-record counter-prefix execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourcePrefix_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (beginSourceRecordCfg tag data)
      (some (scanTargetCfg tag (afterSourcePrefixData data)))
      (sourcePrefixTime data) := by
  have begin := oneStep (step_beginSourceRecord tag data)
  have begin' : EvalsToInTime machine.step
      (beginSourceRecordCfg tag data)
      (some (copyCounterCfg .sourceVertexClause tag
        (beginSourceRecordData data))) 1 := by
    simpa only [beginSourceRecordData] using begin
  have beginScratchEq : (beginSourceRecordData data).scratch = [] := by
    simpa only [beginSourceRecordData] using scratchEq
  have counters := sourceCounters_evalsInTime tag
    (beginSourceRecordData data) beginScratchEq
  have whole := EvalsToInTime.trans machine.step
    1 (sourceCountersTime (beginSourceRecordData data))
    _ _ _ begin' counters
  simpa only [sourcePrefixTime, afterSourcePrefixData] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

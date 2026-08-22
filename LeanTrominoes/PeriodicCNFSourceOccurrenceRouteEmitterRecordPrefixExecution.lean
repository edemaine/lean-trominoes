/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOccurrenceSteps
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecutionData

/-! # One-record counter-prefix execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def recordPrefix_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (beginRecordCfg cursor data)
      (some (scanTargetCfg cursor
        (afterRecordCounters (beginRecordData data))))
      (recordCountersTime (beginRecordData data) + 1) := by
  have begin := oneStep (step_beginRecord cursor data)
  have begin' : EvalsToInTime machine.step
      (beginRecordCfg cursor data)
      (some (copyCounterCfg .vertexClauses cursor (beginRecordData data)))
      1 := by
    simpa only [beginRecordData] using begin
  have beginScratchEq : (beginRecordData data).scratch = [] := by
    simpa only [beginRecordData] using scratchEq
  have counters := recordCounters_evalsInTime cursor
    (beginRecordData data) beginScratchEq
  exact EvalsToInTime.trans machine.step
    1 (recordCountersTime (beginRecordData data))
    (beginRecordCfg cursor data)
    (copyCounterCfg .vertexClauses cursor (beginRecordData data))
    (some (scanTargetCfg cursor
      (afterRecordCounters (beginRecordData data))))
    begin' counters

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

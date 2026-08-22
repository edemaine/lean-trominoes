/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordMissingSuffixExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordPrefixExecution

/-! # Complete missing-target record execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def recordMissing_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = [])
    (targetsEq : data.targets = []) :
    EvalsToInTime machine.step
      (beginRecordCfg cursor data)
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData
          (afterRecordCounters (beginRecordData data)) 0 []
          cursor.literalIndex cursor.currentNext cursor.anchorValue)))
      (recordTime data 0) := by
  have prefixRun := recordPrefix_evalsInTime cursor data scratchEq
  have countersTargetsEq :
      (afterRecordCounters (beginRecordData data)).targets = [] := by
    simpa only [afterRecordCounters_targets, beginRecordData] using targetsEq
  have suffixRun := recordMissingSuffix_evalsInTime cursor
    (afterRecordCounters (beginRecordData data)) countersTargetsEq
  have whole := EvalsToInTime.trans machine.step
    (recordCountersTime (beginRecordData data) + 1)
    (recordSuffixTime 0)
    (beginRecordCfg cursor data)
    (scanTargetCfg cursor (afterRecordCounters (beginRecordData data)))
    (some (scanOccurrencesCfg cursor
      (afterFinishedRecordData
        (afterRecordCounters (beginRecordData data)) 0 []
        cursor.literalIndex cursor.currentNext cursor.anchorValue)))
    prefixRun suffixRun
  simpa only [recordTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterFinishRecordStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTargetNilStep

/-! # Missing-target record suffix execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def recordMissingSuffix_evalsInTime (cursor : Cursor)
    (data : TapeData) (targetsEq : data.targets = []) :
    EvalsToInTime machine.step
      (scanTargetCfg cursor data)
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData data 0 [] cursor.literalIndex
          cursor.currentNext cursor.anchorValue)))
      (recordSuffixTime 0) := by
  have target := oneStep (step_scanTarget_nil cursor data targetsEq)
  have target' : EvalsToInTime machine.step
      (scanTargetCfg cursor data)
      (some (finishRecordCfg cursor.literalIndex cursor.currentNext
        cursor.anchorValue cursor (afterTargetData data 0 []))) 1 := by
    simpa only [afterTargetData, List.replicate_zero,
      List.nil_append, List.singleton_append] using target
  have finish := oneStep
    (step_finishRecord cursor.literalIndex cursor.currentNext
      cursor.anchorValue cursor (afterTargetData data 0 []))
  have finish' : EvalsToInTime machine.step
      (finishRecordCfg cursor.literalIndex cursor.currentNext
        cursor.anchorValue cursor (afterTargetData data 0 []))
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData data 0 [] cursor.literalIndex
          cursor.currentNext cursor.anchorValue))) 1 := by
    simpa only [afterFinishedRecordData] using finish
  have whole := EvalsToInTime.trans machine.step 1 1
    (scanTargetCfg cursor data)
    (finishRecordCfg cursor.literalIndex cursor.currentNext
      cursor.anchorValue cursor (afterTargetData data 0 []))
    (some (scanOccurrencesCfg cursor
      (afterFinishedRecordData data 0 [] cursor.literalIndex
        cursor.currentNext cursor.anchorValue))) target' finish'
  simpa only [recordSuffixTime, Nat.zero_add] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

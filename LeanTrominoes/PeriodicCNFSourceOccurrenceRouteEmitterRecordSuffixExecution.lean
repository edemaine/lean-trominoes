/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterFinishRecordStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTargetExecution

/-! # One-record target-and-suffix execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def recordSuffix_evalsInTime (cursor : Cursor)
    (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol)
    (targetsEq : data.targets =
      List.replicate targetCount .unit ++ .delimiter :: remainingTargets) :
    EvalsToInTime machine.step
      (scanTargetCfg cursor data)
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData data targetCount remainingTargets
          cursor.literalIndex cursor.currentNext cursor.anchorValue)))
      (recordSuffixTime targetCount) := by
  have target := scanTarget_evalsInTime targetCount cursor data
    remainingTargets targetsEq
  have target' : EvalsToInTime machine.step
      (scanTargetCfg cursor data)
      (some (finishRecordCfg cursor.literalIndex cursor.currentNext
        cursor.anchorValue cursor
        (afterTargetData data targetCount remainingTargets)))
      (targetCount + 1) := by
    simpa only [afterTargetData] using target
  have finish := oneStep
    (step_finishRecord cursor.literalIndex cursor.currentNext
      cursor.anchorValue cursor
      (afterTargetData data targetCount remainingTargets))
  have finish' : EvalsToInTime machine.step
      (finishRecordCfg cursor.literalIndex cursor.currentNext
        cursor.anchorValue cursor
        (afterTargetData data targetCount remainingTargets))
      (some (scanOccurrencesCfg cursor
        (afterFinishedRecordData data targetCount remainingTargets
          cursor.literalIndex cursor.currentNext cursor.anchorValue)))
      1 := by
    simpa only [afterFinishedRecordData] using finish
  have whole := EvalsToInTime.trans machine.step
    (targetCount + 1) 1
    (scanTargetCfg cursor data)
    (finishRecordCfg cursor.literalIndex cursor.currentNext
      cursor.anchorValue cursor
      (afterTargetData data targetCount remainingTargets))
    (some (scanOccurrencesCfg cursor
      (afterFinishedRecordData data targetCount remainingTargets
        cursor.literalIndex cursor.currentNext cursor.anchorValue)))
    target' finish'
  simpa only [recordSuffixTime] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSuffixSteps
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetExecution

/-! # Source target-field and suffix execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def sourceTarget_evalsInTime (tag : Tag)
    (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol)
    (targetsEq : data.targets =
      List.replicate targetCount .unit ++ .delimiter :: remainingTargets) :
    EvalsToInTime machine.step
      (scanTargetCfg tag data)
      (some (beginTargetRecordCfg tag
        (afterFinishedSourceData data targetCount remainingTargets tag)))
      (sourceTargetTime targetCount) := by
  have target := scanTarget_evalsInTime targetCount tag data
    remainingTargets targetsEq
  have target' : EvalsToInTime machine.step
      (scanTargetCfg tag data)
      (some (finishSourceTargetCfg tag
        (afterSourceTargetData data targetCount remainingTargets)))
      (targetCount + 1) := by
    simpa only [afterSourceTargetData] using target
  have finish := oneStep
    (step_finishSourceTarget tag
      (afterSourceTargetData data targetCount remainingTargets))
  have finish' : EvalsToInTime machine.step
      (finishSourceTargetCfg tag
        (afterSourceTargetData data targetCount remainingTargets))
      (some (beginTargetRecordCfg tag
        (afterFinishedSourceData data targetCount remainingTargets tag)))
      1 := by
    simpa only [afterFinishedSourceData] using finish
  have whole := EvalsToInTime.trans machine.step
    (targetCount + 1) 1 _ _ _ target' finish'
  simpa only [sourceTargetTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

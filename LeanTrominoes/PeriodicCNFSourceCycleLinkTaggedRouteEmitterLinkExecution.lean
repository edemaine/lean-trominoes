/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourcePrefixExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionProjections
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceTargetExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetRecordExecution

/-! # Complete one-link execution for tagged cycle-link route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def link_evalsInTime (tag : Tag) (data : TapeData)
    (targetCount : Nat) (remainingTargets : List UnarySymbol)
    (targetsEq : data.targets =
      List.replicate targetCount .unit ++ .delimiter :: remainingTargets)
    (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (beginSourceRecordCfg tag data)
      (some (scanLinksCfg tag
        (afterLinkData data targetCount remainingTargets tag)))
      (linkTime data targetCount remainingTargets tag) := by
  have prefixRun := sourcePrefix_evalsInTime tag data scratchEq
  have targetEq : (afterSourcePrefixData data).targets =
      List.replicate targetCount .unit ++ .delimiter :: remainingTargets := by
    simpa only [afterSourcePrefixData_targets] using targetsEq
  have sourceTarget := sourceTarget_evalsInTime tag
    (afterSourcePrefixData data) targetCount remainingTargets targetEq
  have throughSource := EvalsToInTime.trans machine.step
    (sourcePrefixTime data) (sourceTargetTime targetCount)
    _ _ _ prefixRun sourceTarget
  have targetScratch :
      (afterFinishedSourceData (afterSourcePrefixData data)
        targetCount remainingTargets tag).scratch = [] := by
    simp only [afterFinishedSourceData_scratch,
      afterSourcePrefixData_scratch]
  have targetRecord := targetRecord_evalsInTime tag
    (afterFinishedSourceData (afterSourcePrefixData data)
      targetCount remainingTargets tag) targetScratch
  have whole := EvalsToInTime.trans machine.step
    (sourceTargetTime targetCount + sourcePrefixTime data)
    (targetRecordTime
      (afterFinishedSourceData (afterSourcePrefixData data)
        targetCount remainingTargets tag))
    _ _ _ throughSource targetRecord
  simpa only [linkTime, afterLinkData] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

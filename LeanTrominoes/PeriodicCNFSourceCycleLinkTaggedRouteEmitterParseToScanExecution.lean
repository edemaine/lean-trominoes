/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterHeaderExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRestoreTagsExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRestoreTargetsExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetInputExecution

/-! # Parsing a nested separated tagged cycle-link stream -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def parseTime (clauseTotal : Nat) (tags : List Tag)
    (targets : List UnarySymbol) : Nat :=
  2 * clauseTotal + 4 * tags.length + 4 * targets.length + 6

def parsing_evalsInTime (clauseTotal : Nat) (tags : List Tag)
    (targets : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanHeaderCfg initialTag
        ⟨List.replicate clauseTotal (.left (.left .unit)) ++
            .left (.left .delimiter) :: .left .separator ::
              tags.map (fun tag => .left (.right tag)) ++
                .separator :: targets.map .right,
          [], [], [], [], [], [], [], [], [], []⟩)
      (some (scanLinksCfg initialTag
        ⟨[], [], tags, [], targets,
          List.replicate clauseTotal (),
          List.replicate tags.length (), [], [], [], []⟩))
      (parseTime clauseTotal tags targets) := by
  let startData : TapeData :=
    ⟨List.replicate clauseTotal (.left (.left .unit)) ++
        .left (.left .delimiter) :: .left .separator ::
          tags.map (fun tag => .left (.right tag)) ++
            .separator :: targets.map .right,
      [], [], [], [], [], [], [], [], [], []⟩
  let afterHeader : TapeData :=
    ⟨targets.map .right, tags.reverse, [], [], [],
      List.replicate clauseTotal (), List.replicate tags.length (),
      [], [], [], []⟩
  let afterTargets : TapeData :=
    ⟨[], tags.reverse, [], targets.reverse, [],
      List.replicate clauseTotal (), List.replicate tags.length (),
      [], [], [], []⟩
  let afterTags : TapeData :=
    ⟨[], [], tags, targets.reverse, [],
      List.replicate clauseTotal (), List.replicate tags.length (),
      [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], tags, [], targets,
      List.replicate clauseTotal (), List.replicate tags.length (),
      [], [], [], []⟩
  have headerRun := scanHeader_evalsInTime initialTag clauseTotal tags
    (targets.map .right) startData rfl
  have headerRun' : EvalsToInTime machine.step
      (scanHeaderCfg initialTag startData)
      (some (scanTargetsInputCfg initialTag afterHeader))
      (2 * clauseTotal + 2 * tags.length + 3) := by
    simpa [startData, afterHeader] using headerRun
  have targetsRun := scanTargetsInput_evalsInTime initialTag targets
    afterHeader rfl
  have targetsRun' : EvalsToInTime machine.step
      (scanTargetsInputCfg initialTag afterHeader)
      (some (restoreTagsCfg initialTag afterTargets))
      (2 * targets.length + 1) := by
    simpa [afterHeader, afterTargets] using targetsRun
  have throughTargets := EvalsToInTime.trans machine.step
    (2 * clauseTotal + 2 * tags.length + 3)
    (2 * targets.length + 1) _ _ _ headerRun' targetsRun'
  have tagsRun := restoreTags_evalsInTime initialTag tags.reverse
    afterTargets rfl
  have tagsRun' : EvalsToInTime machine.step
      (restoreTagsCfg initialTag afterTargets)
      (some (restoreTargetsCfg initialTag afterTags))
      (2 * tags.length + 1) := by
    simpa [afterTargets, afterTags] using tagsRun
  have throughTags := EvalsToInTime.trans machine.step
    (2 * targets.length + 1 +
      (2 * clauseTotal + 2 * tags.length + 3))
    (2 * tags.length + 1) _ _ _ throughTargets tagsRun'
  have restoreTargetsRun := restoreTargets_evalsInTime initialTag
    targets.reverse afterTags rfl
  have restoreTargetsRun' : EvalsToInTime machine.step
      (restoreTargetsCfg initialTag afterTags)
      (some (scanLinksCfg initialTag parsedData))
      (2 * targets.length + 1) := by
    simpa [afterTags, parsedData] using restoreTargetsRun
  have whole := EvalsToInTime.trans machine.step
    (2 * tags.length + 1 +
      (2 * targets.length + 1 +
        (2 * clauseTotal + 2 * tags.length + 3)))
    (2 * targets.length + 1) _ _ _ throughTags restoreTargetsRun'
  convert whole using 1
  simp [parseTime]
  omega

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

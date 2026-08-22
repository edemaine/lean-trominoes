/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.GetD
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTagSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInput
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndices

/-! # Semantics of tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF

namespace SourceCycleLinkTaggedRouteEmitter

def ofGroupInput (input : SourceCycleLinkRouteEmitter.Input) : Input where
  clauseCount := input.clauseCount
  tags := SourceCycleLinkPositionTags.tags input.groupSizes
  targets := SourceCycleLinkTargetIndices.targetIndices input.groupSizes
  valid := by simp

@[simp] theorem ofGroupInput_clauseCount
    (input : SourceCycleLinkRouteEmitter.Input) :
    (ofGroupInput input).clauseCount = input.clauseCount := rfl

@[simp] theorem ofGroupInput_literalCount
    (input : SourceCycleLinkRouteEmitter.Input) :
    (ofGroupInput input).literalCount = input.literalCount := by
  simp [ofGroupInput, Input.literalCount,
    SourceCycleLinkRouteEmitter.Input.literalCount]

theorem sourceRank_groupTags_getElem (groupSize position : Nat)
    (positionLt : position < groupSize) :
    SourceCycleLinkPositionTags.sourceTargetPortRank
        ((SourceCycleLinkPositionTags.groupTags groupSize)[position]'(by
          simpa using positionLt)) =
      (if position = 0 then 1 else 2) := by
  have mapped :=
    SourceCycleLinkPositionTags.map_sourceTargetPortRank_groupTags groupSize
  have leftLt : position <
      ((SourceCycleLinkPositionTags.groupTags groupSize).map
        SourceCycleLinkPositionTags.sourceTargetPortRank).length := by
    simpa using positionLt
  have rightLt : position <
      (SourceCycleLinkPositionTags.sourceRanks groupSize).length := by
    simp [SourceCycleLinkPositionTags.sourceRanks]
    exact positionLt
  have point := congrArg (fun values : List Nat => values.getD position 1)
    mapped
  rw [List.getD_eq_getElem _ _ leftLt,
    List.getD_eq_getElem _ _ rightLt] at point
  simpa [SourceCycleLinkPositionTags.sourceRanks] using point

theorem targetRank_groupTags_getElem (groupSize position : Nat)
    (positionLt : position < groupSize) :
    SourceCycleLinkPositionTags.targetTargetPortRank
        ((SourceCycleLinkPositionTags.groupTags groupSize)[position]'(by
          simpa using positionLt)) =
      (if position + 1 = groupSize then 2 else 1) := by
  have mapped :=
    SourceCycleLinkPositionTags.map_targetTargetPortRank_groupTags groupSize
  have leftLt : position <
      ((SourceCycleLinkPositionTags.groupTags groupSize).map
        SourceCycleLinkPositionTags.targetTargetPortRank).length := by
    simpa using positionLt
  have rightLt : position <
      (SourceCycleLinkPositionTags.targetRanks groupSize).length := by
    simp [SourceCycleLinkPositionTags.targetRanks]
    exact positionLt
  have point := congrArg (fun values : List Nat => values.getD position 1)
    mapped
  rw [List.getD_eq_getElem _ _ leftLt,
    List.getD_eq_getElem _ _ rightLt] at point
  simpa [SourceCycleLinkPositionTags.targetRanks] using point

theorem sourceFields_group_getElem
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize position : Nat)
    (positionLt : position < groupSize) :
    sourceFields (ofGroupInput input) (blockStart + position)
        ((SourceCycleLinkTargetIndices.groupTargetIndices
          blockStart groupSize)[position]'(by simpa using positionLt))
        ((SourceCycleLinkPositionTags.groupTags groupSize)[position]'(by
          simpa using positionLt)) =
      SourceCycleLinkRouteEmitter.sourceFields input groupSize
        (blockStart + position) position := by
  have sourceRank := sourceRank_groupTags_getElem
    groupSize position positionLt
  have targetIndex :
      (SourceCycleLinkTargetIndices.groupTargetIndices
        blockStart groupSize)[position]'(by simpa using positionLt) =
        SourceCycleLinkTargetIndices.targetIndex
          blockStart groupSize position := by
    simp [SourceCycleLinkTargetIndices.groupTargetIndices]
  by_cases positionZero : position = 0
  · subst position
    simp [sourceFields, SourceCycleLinkRouteEmitter.sourceFields,
      ofGroupInput_literalCount, sourceRank, targetIndex,
      SourceCycleLinkTargetIndices.targetIndex]
  · simp [sourceFields, SourceCycleLinkRouteEmitter.sourceFields,
      ofGroupInput_literalCount, sourceRank, targetIndex,
      SourceCycleLinkTargetIndices.targetIndex, positionZero]

theorem targetFields_group_getElem
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize position : Nat)
    (positionLt : position < groupSize) :
    targetFields (ofGroupInput input) (blockStart + position)
        ((SourceCycleLinkPositionTags.groupTags groupSize)[position]'(by
          simpa using positionLt)) =
      SourceCycleLinkRouteEmitter.targetFields input groupSize
        (blockStart + position) position := by
  have targetRank := targetRank_groupTags_getElem
    groupSize position positionLt
  simp [targetFields, SourceCycleLinkRouteEmitter.targetFields,
    ofGroupInput_literalCount, targetRank]

theorem linkTokens_group_getElem
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize position : Nat)
    (positionLt : position < groupSize) :
    linkTokens (ofGroupInput input) (blockStart + position)
        ((SourceCycleLinkTargetIndices.groupTargetIndices
          blockStart groupSize)[position]'(by simpa using positionLt))
        ((SourceCycleLinkPositionTags.groupTags groupSize)[position]'(by
          simpa using positionLt)) =
      SourceCycleLinkRouteEmitter.linkTokens input groupSize
        (blockStart + position) position := by
  unfold linkTokens SourceCycleLinkRouteEmitter.linkTokens
  rw [sourceFields_group_getElem input blockStart groupSize position
      positionLt,
    targetFields_group_getElem input blockStart groupSize position positionLt]

def taggedBlocks (input : Input) (linkIndex : Nat)
    (tags : List Tag) (targets : List Nat) :
    List (List UnaryProgramTokens.Token) :=
  ((tags.zip targets).zipIdx linkIndex).map fun entry =>
    linkTokens input entry.2 entry.1.2 entry.1.1

theorem emitAux_eq_taggedBlocks_flatten (input : Input) (linkIndex : Nat)
    (tags : List Tag) (targets : List Nat)
    (lengthEq : tags.length = targets.length) :
    emitAux input linkIndex tags targets =
      (taggedBlocks input linkIndex tags targets).flatten := by
  induction tags generalizing targets linkIndex with
  | nil =>
      have targetsNil : targets = [] := List.eq_nil_of_length_eq_zero
        lengthEq.symm
      subst targets
      rfl
  | cons tag tags induction =>
      cases targets with
      | nil => simp at lengthEq
      | cons target targets =>
          have tailLength : tags.length = targets.length := by
            simpa using lengthEq
          simp only [emitAux, taggedBlocks, List.zip_cons_cons,
            List.zipIdx_cons, List.map_cons, List.flatten_cons]
          rw [induction (linkIndex + 1) targets tailLength]
          rfl

theorem taggedBlocks_group_eq
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize : Nat) :
    taggedBlocks (ofGroupInput input) blockStart
        (SourceCycleLinkPositionTags.groupTags groupSize)
        (SourceCycleLinkTargetIndices.groupTargetIndices
          blockStart groupSize) =
      (List.range groupSize).map fun position =>
        SourceCycleLinkRouteEmitter.linkTokens input groupSize
          (blockStart + position) position := by
  apply List.ext_getElem
  · simp [taggedBlocks]
  · intro position leftBound rightBound
    have positionLt : position < groupSize := by
      simpa [taggedBlocks] using leftBound
    simp only [taggedBlocks, List.getElem_map, List.getElem_zipIdx,
      List.getElem_zip, List.getElem_range]
    exact linkTokens_group_getElem input blockStart groupSize position
      positionLt

theorem emitAux_group_eq
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize : Nat) :
    emitAux (ofGroupInput input) blockStart
        (SourceCycleLinkPositionTags.groupTags groupSize)
        (SourceCycleLinkTargetIndices.groupTargetIndices
          blockStart groupSize) =
      SourceCycleLinkRouteEmitter.groupTokens input blockStart groupSize := by
  rw [emitAux_eq_taggedBlocks_flatten _ _ _ _ (by simp),
    taggedBlocks_group_eq]
  unfold SourceCycleLinkRouteEmitter.groupTokens
  induction List.range groupSize with
  | nil => rfl
  | cons position positions induction =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons,
        induction]

theorem emitAux_append (input : Input) (linkIndex : Nat)
    (firstTags secondTags : List Tag) (firstTargets secondTargets : List Nat)
    (lengthEq : firstTags.length = firstTargets.length) :
    emitAux input linkIndex (firstTags ++ secondTags)
        (firstTargets ++ secondTargets) =
      emitAux input linkIndex firstTags firstTargets ++
        emitAux input (linkIndex + firstTags.length)
          secondTags secondTargets := by
  induction firstTags generalizing firstTargets linkIndex with
  | nil =>
      have targetsNil : firstTargets = [] := List.eq_nil_of_length_eq_zero
        lengthEq.symm
      subst firstTargets
      simp [emitAux]
  | cons tag tags induction =>
      cases firstTargets with
      | nil => simp at lengthEq
      | cons target targets =>
          have tailLength : tags.length = targets.length := by
            simpa using lengthEq
          simp only [List.cons_append, emitAux]
          rw [induction (linkIndex + 1) targets tailLength]
          simp [List.append_assoc, Nat.add_comm,
            Nat.add_left_comm]

theorem emitAux_groups_eq (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart : Nat) (groupSizes : List Nat) :
    emitAux (ofGroupInput input) blockStart
        (SourceCycleLinkPositionTags.tags groupSizes)
        (SourceCycleLinkTargetIndices.targetIndicesAux
          blockStart groupSizes) =
      SourceCycleLinkRouteEmitter.groupsTokensAux input
        blockStart groupSizes := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [SourceCycleLinkPositionTags.tags,
        List.flatMap_cons,
        SourceCycleLinkTargetIndices.targetIndicesAux,
        emitAux_append _ _ _ _ _ _ (by simp),
        emitAux_group_eq,
        SourceCycleLinkRouteEmitter.groupsTokensAux]
      rw [← SourceCycleLinkPositionTags.tags]
      rw [SourceCycleLinkPositionTags.groupTags_length,
        induction (blockStart + groupSize)]

theorem emit_ofGroupInput
    (input : SourceCycleLinkRouteEmitter.Input) :
    emit (ofGroupInput input) = SourceCycleLinkRouteEmitter.emit input := by
  exact emitAux_groups_eq input 0 input.groupSizes

end SourceCycleLinkTaggedRouteEmitter

end LeanTrominoes.PeriodicCNF

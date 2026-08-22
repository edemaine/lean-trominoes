/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterSkeleton

/-! # Varying projections of cycle-link emitter descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceCycleLinkRouteEmitter

@[simp] theorem linkDescriptors_length
    (input : Input) (groupSize linkIndex position : Nat) :
    (linkDescriptors input groupSize linkIndex position).length = 2 := by
  rfl

@[simp] theorem groupDescriptors_length
    (input : Input) (blockStart groupSize : Nat) :
    (groupDescriptors input blockStart groupSize).length =
      2 * groupSize := by
  simp [groupDescriptors]
  omega

@[simp] theorem groupsDescriptorsAux_length
    (input : Input) (blockStart : Nat) (groupSizes : List Nat) :
    (groupsDescriptorsAux input blockStart groupSizes).length =
      2 * groupSizes.sum := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [groupsDescriptorsAux, List.length_append,
        groupDescriptors_length, induction]
      simp only [List.sum_cons]
      omega

@[simp] theorem descriptors_length (input : Input) :
    (descriptors input).length = 2 * input.literalCount := by
  simp [descriptors, Input.literalCount]

theorem groupDescriptors_targetVertexIndices
    (input : Input) (blockStart groupSize : Nat) :
    (groupDescriptors input blockStart groupSize).map
        (·.targetVertexIndex) =
      PeriodicThreeSATThree.CycleLinkDescriptorStreams.groupTargetIndexWord
        blockStart groupSize := by
  unfold groupDescriptors
    PeriodicThreeSATThree.CycleLinkDescriptorStreams.groupTargetIndexWord
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro position positionMember
  rw [List.mem_range] at positionMember
  simp only [linkDescriptors, List.map_cons, List.map_nil]
  simp [sourceDescriptor, targetDescriptor]

theorem groupsDescriptorsAux_targetVertexIndices
    (input : Input) (blockStart : Nat) (groupSizes : List Nat) :
    (groupsDescriptorsAux input blockStart groupSizes).map
        (·.targetVertexIndex) =
      PeriodicThreeSATThree.CycleLinkDescriptorStreams.targetIndexWordsAux
        blockStart groupSizes := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [groupsDescriptorsAux, List.map_append,
        groupDescriptors_targetVertexIndices,
        induction (blockStart + groupSize)]
      rfl

theorem descriptors_targetVertexIndices (input : Input) :
    (descriptors input).map (·.targetVertexIndex) =
      PeriodicThreeSATThree.CycleLinkDescriptorStreams.targetIndexWordsAux
        0 input.groupSizes := by
  exact groupsDescriptorsAux_targetVertexIndices
    input 0 input.groupSizes

theorem groupDescriptors_targetPortRanks
    (input : Input) (blockStart groupSize : Nat) :
    (groupDescriptors input blockStart groupSize).map
        (·.targetPortRank) =
      PeriodicThreeSATThree.CycleLinkGroupedPortRanks.positionalRankWord
        groupSize := by
  unfold groupDescriptors
    PeriodicThreeSATThree.CycleLinkGroupedPortRanks.positionalRankWord
    PeriodicThreeSATThree.CycleLinkGroupedPortRanks.positionRankBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro position _
  rfl

theorem groupsDescriptorsAux_targetPortRanks
    (input : Input) (blockStart : Nat) (groupSizes : List Nat) :
    (groupsDescriptorsAux input blockStart groupSizes).map
        (·.targetPortRank) =
      groupSizes.flatMap
        PeriodicThreeSATThree.CycleLinkGroupedPortRanks.positionalRankWord := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [groupsDescriptorsAux, List.map_append,
        groupDescriptors_targetPortRanks,
        induction (blockStart + groupSize), List.flatMap_cons]

theorem descriptors_targetPortRanks (input : Input) :
    (descriptors input).map (·.targetPortRank) =
      input.groupSizes.flatMap
        PeriodicThreeSATThree.CycleLinkGroupedPortRanks.positionalRankWord := by
  exact groupsDescriptorsAux_targetPortRanks input 0 input.groupSizes

end SourceCycleLinkRouteEmitter
end PeriodicCNF
end LeanTrominoes

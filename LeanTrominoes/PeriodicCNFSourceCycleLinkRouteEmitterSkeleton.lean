/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterDescriptors
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPositionTargetIndexWord

/-! # Target-erased skeleton of cycle-link emitter descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceCycleLinkRouteEmitter

def eraseTargetData
    (descriptor : PeriodicOrthocrossing.RouteDescriptor) :
    PeriodicOrthocrossing.RouteDescriptor :=
  { descriptor with targetVertexIndex := 0, targetPortRank := 0 }

def sourceSkeleton (input : Input) (linkIndex : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := input.clauseCount + 2 * input.literalCount
  edgeCount := 3 * input.literalCount
  edgeIndex := input.literalCount + 2 * linkIndex
  sourceVertexIndex :=
    input.literalCount + input.clauseCount + linkIndex
  targetVertexIndex := 0
  sourcePortRank := 0
  targetPortRank := 0
  offset := (0, 0)

def targetSkeleton (input : Input) (linkIndex : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := input.clauseCount + 2 * input.literalCount
  edgeCount := 3 * input.literalCount
  edgeIndex := input.literalCount + 2 * linkIndex + 1
  sourceVertexIndex :=
    input.literalCount + input.clauseCount + linkIndex
  targetVertexIndex := 0
  sourcePortRank := 1
  targetPortRank := 0
  offset := (0, 0)

def skeletonBlock (input : Input) (linkIndex : Nat) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  [sourceSkeleton input linkIndex, targetSkeleton input linkIndex]

def skeletons (input : Input) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  (List.range input.literalCount).flatMap (skeletonBlock input)

@[simp] theorem map_eraseTargetData_linkDescriptors
    (input : Input) (groupSize linkIndex position : Nat) :
    (linkDescriptors input groupSize linkIndex position).map
        eraseTargetData =
      skeletonBlock input linkIndex := by
  rfl

theorem map_eraseTargetData_groupDescriptors
    (input : Input) (blockStart groupSize : Nat) :
    (groupDescriptors input blockStart groupSize).map eraseTargetData =
      (List.range groupSize).flatMap fun position =>
        skeletonBlock input (blockStart + position) := by
  unfold groupDescriptors
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro position _
  exact map_eraseTargetData_linkDescriptors
    input groupSize (blockStart + position) position

theorem range_flatMap_add_split
    {Output : Type*} (block : Nat → List Output)
    (start first second : Nat) :
    (List.range (first + second)).flatMap
        (fun index => block (start + index)) =
      (List.range first).flatMap (fun index => block (start + index)) ++
        (List.range second).flatMap
          (fun index => block ((start + first) + index)) := by
  calc
    (List.range (first + second)).flatMap
        (fun index => block (start + index)) =
        ((List.range (first + second)).map
          (fun index => start + index)).flatMap block := by
      rw [List.flatMap_map]
    _ = (((List.range first).map (fun index => start + index)) ++
          ((List.range second).map
            (fun index => (start + first) + index))).flatMap block := by
      rw [PeriodicThreeSATThree.CycleLinkGroupedTargetIndices.map_range_add_split]
    _ = _ := by
      rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]

theorem map_eraseTargetData_groupsDescriptorsAux
    (input : Input) (blockStart : Nat) (groupSizes : List Nat) :
    (groupsDescriptorsAux input blockStart groupSizes).map
        eraseTargetData =
      (List.range groupSizes.sum).flatMap fun position =>
        skeletonBlock input (blockStart + position) := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [groupsDescriptorsAux, List.map_append,
        map_eraseTargetData_groupDescriptors,
        induction (blockStart + groupSize), List.sum_cons,
        range_flatMap_add_split]

/-- Erasing the two varying target fields leaves one canonical source/target
skeleton block for every global link index. -/
theorem map_eraseTargetData_descriptors (input : Input) :
    (descriptors input).map eraseTargetData = skeletons input := by
  unfold descriptors skeletons Input.literalCount
  simpa only [zero_add] using
    map_eraseTargetData_groupsDescriptorsAux input 0 input.groupSizes

end SourceCycleLinkRouteEmitter
end PeriodicCNF
end LeanTrominoes

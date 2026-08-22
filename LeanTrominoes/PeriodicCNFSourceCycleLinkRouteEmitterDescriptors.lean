/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndices
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData

/-! # Numeric descriptors denoted by the source cycle-link emitter -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceCycleLinkRouteEmitter

def sourceDescriptor (input : Input)
    (groupSize linkIndex position : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := input.clauseCount + 2 * input.literalCount
  edgeCount := 3 * input.literalCount
  edgeIndex := input.literalCount + 2 * linkIndex
  sourceVertexIndex :=
    input.literalCount + input.clauseCount + linkIndex
  targetVertexIndex :=
    SourceCycleLinkTargetIndices.targetIndex
      (linkIndex - position) groupSize position
  sourcePortRank := 0
  targetPortRank := if position = 0 then 1 else 2
  offset := (0, 0)

def targetDescriptor (input : Input)
    (groupSize linkIndex position : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := input.clauseCount + 2 * input.literalCount
  edgeCount := 3 * input.literalCount
  edgeIndex := input.literalCount + 2 * linkIndex + 1
  sourceVertexIndex :=
    input.literalCount + input.clauseCount + linkIndex
  targetVertexIndex := linkIndex
  sourcePortRank := 1
  targetPortRank := if position + 1 = groupSize then 2 else 1
  offset := (0, 0)

def linkDescriptors (input : Input)
    (groupSize linkIndex position : Nat) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  [sourceDescriptor input groupSize linkIndex position,
    targetDescriptor input groupSize linkIndex position]

def groupDescriptors (input : Input)
    (blockStart groupSize : Nat) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  (List.range groupSize).flatMap fun position =>
    linkDescriptors input groupSize (blockStart + position) position

def groupsDescriptorsAux (input : Input) : Nat → List Nat →
    List PeriodicOrthocrossing.RouteDescriptor
  | _, [] => []
  | blockStart, groupSize :: groupSizes =>
      groupDescriptors input blockStart groupSize ++
        groupsDescriptorsAux input (blockStart + groupSize) groupSizes

def descriptors (input : Input) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  groupsDescriptorsAux input 0 input.groupSizes

theorem sourceDescriptor_unaryFields
    (input : Input) (groupSize linkIndex position : Nat)
    (positionLe : position ≤ linkIndex) :
    (sourceDescriptor input groupSize linkIndex position).unaryFields =
      sourceFields input groupSize linkIndex position := by
  by_cases positionZero : position = 0
  · subst position
    simp [sourceDescriptor, sourceFields,
      SourceCycleLinkTargetIndices.targetIndex,
      PeriodicOrthocrossing.RouteDescriptor.unaryFields,
      PeriodicOrthocrossing.signedUnaryFields]
  · simp [sourceDescriptor, sourceFields,
      SourceCycleLinkTargetIndices.targetIndex,
      PeriodicOrthocrossing.RouteDescriptor.unaryFields,
      PeriodicOrthocrossing.signedUnaryFields, positionZero]
    omega

theorem targetDescriptor_unaryFields
    (input : Input) (groupSize linkIndex position : Nat) :
    (targetDescriptor input groupSize linkIndex position).unaryFields =
      targetFields input groupSize linkIndex position := by
  simp [targetDescriptor, targetFields,
    PeriodicOrthocrossing.RouteDescriptor.unaryFields,
    PeriodicOrthocrossing.signedUnaryFields]

theorem routeDescriptorTokens_append
    (first second : List PeriodicOrthocrossing.RouteDescriptor) :
    PeriodicOrthocrossing.routeDescriptorTokens (first ++ second) =
      PeriodicOrthocrossing.routeDescriptorTokens first ++
        PeriodicOrthocrossing.routeDescriptorTokens second := by
  simp [PeriodicOrthocrossing.routeDescriptorTokens,
    PeriodicOrthocrossing.routeDescriptorFieldBlocks,
    CountedUnaryFieldTokens.countedFieldBlocks]

theorem linkTokens_eq_routeDescriptorTokens
    (input : Input) (groupSize linkIndex position : Nat)
    (positionLe : position ≤ linkIndex) :
    linkTokens input groupSize linkIndex position =
      PeriodicOrthocrossing.routeDescriptorTokens
        (linkDescriptors input groupSize linkIndex position) := by
  unfold linkTokens linkDescriptors
  simp only [PeriodicOrthocrossing.routeDescriptorTokens,
    PeriodicOrthocrossing.routeDescriptorFieldBlocks,
    List.map_cons, List.map_nil,
    CountedUnaryFieldTokens.countedFieldBlocks,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [sourceDescriptor_unaryFields input groupSize linkIndex position
      positionLe,
    targetDescriptor_unaryFields]

theorem groupTokens_eq_routeDescriptorTokens
    (input : Input) (blockStart groupSize : Nat) :
    groupTokens input blockStart groupSize =
      PeriodicOrthocrossing.routeDescriptorTokens
        (groupDescriptors input blockStart groupSize) := by
  unfold groupTokens groupDescriptors
  induction List.range groupSize with
  | nil => rfl
  | cons position positions induction =>
      simp only [List.flatMap_cons]
      rw [linkTokens_eq_routeDescriptorTokens input groupSize
          (blockStart + position) position (by omega),
        routeDescriptorTokens_append, induction]

theorem groupsTokensAux_eq_routeDescriptorTokens
    (input : Input) (blockStart : Nat) (groupSizes : List Nat) :
    groupsTokensAux input blockStart groupSizes =
      PeriodicOrthocrossing.routeDescriptorTokens
        (groupsDescriptorsAux input blockStart groupSizes) := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [groupsTokensAux, groupsDescriptorsAux,
        groupTokens_eq_routeDescriptorTokens,
        routeDescriptorTokens_append,
        induction (blockStart + groupSize)]

theorem emit_eq_routeDescriptorTokens_descriptors (input : Input) :
    emit input =
      PeriodicOrthocrossing.routeDescriptorTokens (descriptors input) := by
  exact groupsTokensAux_eq_routeDescriptorTokens input 0 input.groupSizes

end SourceCycleLinkRouteEmitter
end PeriodicCNF
end LeanTrominoes

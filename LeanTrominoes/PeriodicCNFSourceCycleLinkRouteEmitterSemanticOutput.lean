/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorListExt
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorProjections

/-! # Exact semantic output of the source cycle-link route emitter -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceCycleLinkRouteEmitter

/-- The emitter's explicit numeric descriptors are exactly the actual
cycle-link suffix descriptors of the occurrence-split formula. -/
theorem cycleLinkRouteDescriptors_eq_descriptors
    (source : SourceSplitRouteDescriptorTokens.Source) :
    PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula =
      descriptors (sourceInput source) := by
  let actual :=
    PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula
  let emitted := descriptors (sourceInput source)
  have skeletonEq : actual.map eraseTargetData =
      emitted.map eraseTargetData := by
    change
      (PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula).map
          eraseTargetData =
        (descriptors (sourceInput source)).map eraseTargetData
    rw [LeanTrominoes.PeriodicThreeSATThree.CycleLinkDescriptorStreams.map_eraseTargetData_cycleLinkRouteDescriptors,
      map_eraseTargetData_descriptors]
  have vertexCountEq : actual.map (·.vertexCount) =
      emitted.map (·.vertexCount) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.vertexCount) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have edgeCountEq : actual.map (·.edgeCount) =
      emitted.map (·.edgeCount) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.edgeCount) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have edgeIndexEq : actual.map (·.edgeIndex) =
      emitted.map (·.edgeIndex) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.edgeIndex) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have sourceVertexIndexEq : actual.map (·.sourceVertexIndex) =
      emitted.map (·.sourceVertexIndex) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.sourceVertexIndex) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have sourcePortRankEq : actual.map (·.sourcePortRank) =
      emitted.map (·.sourcePortRank) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.sourcePortRank) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have offsetEq : actual.map (·.offset) = emitted.map (·.offset) := by
    have projected := congrArg
      (List.map fun descriptor : PeriodicOrthocrossing.RouteDescriptor =>
        descriptor.offset) skeletonEq
    simpa only [List.map_map, Function.comp_def, eraseTargetData]
      using projected
  have targetVertexIndexEq : actual.map (·.targetVertexIndex) =
      emitted.map (·.targetVertexIndex) := by
    change
      (PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula).map
          (·.targetVertexIndex) =
        (descriptors (sourceInput source)).map (·.targetVertexIndex)
    rw [LeanTrominoes.PeriodicThreeSATThree.CycleLinkDescriptorStreams.cycleLinkRouteDescriptors_targetVertexIndices,
      descriptors_targetVertexIndices]
  have targetPortRankEq : actual.map (·.targetPortRank) =
      emitted.map (·.targetPortRank) := by
    change
      (PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula).map
          (·.targetPortRank) =
        (descriptors (sourceInput source)).map (·.targetPortRank)
    rw [LeanTrominoes.PeriodicThreeSATThree.CycleLinkDescriptorStreams.cycleLinkRouteDescriptors_targetPortRanks,
      descriptors_targetPortRanks]
  apply PeriodicOrthocrossing.RouteDescriptor.list_ext
  · exact LeanTrominoes.PeriodicThreeSATThree.CycleLinkDescriptorStreams.cycleLinkRouteDescriptors_length_eq_emitter
      source
  · exact vertexCountEq
  · exact edgeCountEq
  · exact edgeIndexEq
  · exact sourceVertexIndexEq
  · exact targetVertexIndexEq
  · exact sourcePortRankEq
  · exact targetPortRankEq
  · exact offsetEq

/-- On a promised flat source, the semantic cycle-link emitter produces
exactly the counted unary token stream of the actual cycle-link descriptors. -/
theorem emit_sourceInput_eq_cycleLinkRouteDescriptorTokens
    (source : SourceSplitRouteDescriptorTokens.Source) :
    emit (sourceInput source) =
      PeriodicOrthocrossing.routeDescriptorTokens
        (PeriodicThreeSATThree.cycleLinkRouteDescriptors
          source.formula) := by
  rw [emit_eq_routeDescriptorTokens_descriptors,
    cycleLinkRouteDescriptors_eq_descriptors]

end SourceCycleLinkRouteEmitter
end PeriodicCNF
end LeanTrominoes

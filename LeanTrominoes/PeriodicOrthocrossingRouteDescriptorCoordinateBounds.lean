/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBounds
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Coordinate bounds for semantic route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- One signed drawing coordinate lies strictly inside a descriptor's
fundamental period. -/
def RouteDescriptor.CoordinateInPeriod
    (descriptor : RouteDescriptor) (coordinate : Int) : Prop :=
  0 < coordinate ∧ coordinate < descriptor.gridSize

/-- Bounds for the seven unshifted coordinates used by a descriptor route. -/
structure RouteDescriptor.CoordinateBounds
    (descriptor : RouteDescriptor) : Prop where
  sourceCenter : descriptor.CoordinateInPeriod
    (vertexX descriptor.sourceVertexIndex)
  targetCenter : descriptor.CoordinateInPeriod
    (vertexX descriptor.targetVertexIndex)
  sourcePort : descriptor.CoordinateInPeriod
    (descriptorPortX descriptor.sourceVertexIndex descriptor.sourcePortRank)
  targetPort : descriptor.CoordinateInPeriod
    (descriptorPortX descriptor.targetVertexIndex descriptor.targetPortRank)
  lowTrack : descriptor.CoordinateInPeriod
    (edgeTrack descriptor.edgeIndex)
  highTrack : descriptor.CoordinateInPeriod
    (edgeTrack descriptor.edgeIndex + 1)
  gate : descriptor.CoordinateInPeriod
    (8 * (descriptor.vertexCount : Int) + 4 + 2 * descriptor.edgeIndex)

/-- Every unshifted coordinate used by a semantic route descriptor lies
strictly inside its drawing period. -/
theorem routeDescriptor_coordinateBounds
    {Vertex : Type} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {tagged : PeriodicEdge Vertex × Nat}
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    (routeDescriptor graph tagged.1 tagged.2).CoordinateBounds := by
  have endpoints := wellFormed.2 tagged.1
    (List.fst_mem_of_mem_zipIdx taggedMember)
  have sourceCenterBounds := vertexX_bounds endpoints.1
  have targetCenterBounds := vertexX_bounds endpoints.2
  have sourcePortBounds := portX_bounds wellFormed degree
    (sourcePort_mem_allPorts graph taggedMember)
  have targetPortBounds := portX_bounds wellFormed degree
    (targetPort_mem_allPorts graph taggedMember)
  have trackBounds := edgeTrack_bounds graph taggedMember
  have gateBounds := edgeGateX_bounds graph taggedMember
  constructor
  · simpa [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize, drawingGridSize] using sourceCenterBounds
  · simpa [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize, drawingGridSize] using targetCenterBounds
  · simpa [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize, descriptorPortX, portX, sourcePort,
      drawingGridSize] using sourcePortBounds
  · simpa [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize, descriptorPortX, portX, targetPort,
      drawingGridSize] using targetPortBounds
  · simp only [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize]
    constructor
    · omega
    · simpa [drawingGridSize] using
        (lt_trans (lt_add_one (edgeTrack tagged.2)) trackBounds.2)
  · simp only [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize]
    constructor
    · omega
    · simpa [drawingGridSize] using trackBounds.2
  · simpa [RouteDescriptor.CoordinateInPeriod, routeDescriptor,
      RouteDescriptor.gridSize, edgeGateX, drawingGridSize] using gateBounds

end LeanTrominoes.PeriodicOrthocrossing

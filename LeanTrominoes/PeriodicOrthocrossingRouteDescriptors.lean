/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstruction

/-! # Numeric descriptors for constructed orthocrossing routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The finite numeric data on which one constructed orthocrossing route
actually depends. -/
structure RouteDescriptor where
  vertexCount : Nat
  edgeCount : Nat
  edgeIndex : Nat
  sourceVertexIndex : Nat
  targetVertexIndex : Nat
  sourcePortRank : Nat
  targetPortRank : Nat
  offset : Cell
  deriving DecidableEq, Repr

/-- Grid size computed from the two presentation lengths. -/
def RouteDescriptor.gridSize (descriptor : RouteDescriptor) : Nat :=
  16 * (descriptor.vertexCount + descriptor.edgeCount + 1)

/-- Port column computed from a vertex index and its local port rank. -/
def descriptorPortX (vertexIndex rank : Nat) : Int :=
  vertexX vertexIndex + 2 * (rank : Int) - 2

/-- The central track portion computed only from one numeric descriptor. -/
def RouteDescriptor.core (descriptor : RouteDescriptor) : List Cell :=
  let size : Int := descriptor.gridSize
  let sourceX :=
    descriptorPortX descriptor.sourceVertexIndex descriptor.sourcePortRank
  let targetX :=
    descriptorPortX descriptor.targetVertexIndex descriptor.targetPortRank
  let sourcePoint : Cell := (sourceX, 3)
  let targetPoint : Cell :=
    Cell.add (targetX, 3) (Cell.scale size descriptor.offset)
  let low := edgeTrack descriptor.edgeIndex
  let high := low + 1
  let gate := 8 * descriptor.vertexCount + 4 + 2 * descriptor.edgeIndex
  match descriptor.offset with
  | (0, 0) =>
      [sourcePoint, (sourceX, low), (targetX, low), targetPoint]
  | (1, 0) =>
      if targetX < sourceX then
        [sourcePoint, (sourceX, low), (size + targetX, low), targetPoint]
      else
        [sourcePoint, (sourceX, low), (size, low), (size, high),
          (size + targetX, high), targetPoint]
  | (-1, 0) =>
      if sourceX < targetX then
        [sourcePoint, (sourceX, low), (targetX - size, low), targetPoint]
      else
        [sourcePoint, (sourceX, low), (0, low), (0, high),
          (targetX - size, high), targetPoint]
  | (0, 1) =>
      [sourcePoint, (sourceX, high), (gate, high), (gate, size + low),
        (targetX, size + low), targetPoint]
  | (0, -1) =>
      [sourcePoint, (sourceX, low), (gate, low), (gate, high - size),
        (targetX, high - size), targetPoint]
  | _ =>
      [sourcePoint, (sourceX, low), (targetPoint.1, low), targetPoint]

/-- Complete orthocrossing route reconstructed from its numeric descriptor. -/
def RouteDescriptor.route (descriptor : RouteDescriptor) : List Cell :=
  let sourceCenter := vertexX descriptor.sourceVertexIndex
  let targetCenter := vertexX descriptor.targetVertexIndex
  let sourceColumn :=
    descriptorPortX descriptor.sourceVertexIndex descriptor.sourcePortRank
  let targetColumn :=
    descriptorPortX descriptor.targetVertexIndex descriptor.targetPortRank
  let targetTranslate :=
    Cell.scale (descriptor.gridSize : Int) descriptor.offset
  let sourceFanout := fanout sourceCenter sourceColumn
  let targetFanout :=
    translatePolyline targetTranslate
      (fanout targetCenter targetColumn).reverse
  joinPolylines
    (joinPolylines sourceFanout descriptor.core)
    targetFanout

/-- Extract the numeric descriptor of one indexed semantic edge. -/
def routeDescriptor {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) : RouteDescriptor where
  vertexCount := graph.vertices.length
  edgeCount := graph.edges.length
  edgeIndex := edgeIndex
  sourceVertexIndex := graph.vertices.idxOf edge.source
  targetVertexIndex := graph.vertices.idxOf edge.target
  sourcePortRank := portRank graph (sourcePort edge edgeIndex)
  targetPortRank := portRank graph (targetPort edge edgeIndex)
  offset := edge.offset

/-- The semantic track constructor factors exactly through its numeric
descriptor. -/
theorem constructedEdgeRoute_eq_descriptorRoute
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    constructedEdgeRoute graph edge edgeIndex =
      (routeDescriptor graph edge edgeIndex).route := by
  rfl

/-- Numeric route descriptors in edge-presentation order. -/
def routeDescriptors {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List RouteDescriptor :=
  graph.edges.zipIdx.map fun tagged =>
    routeDescriptor graph tagged.1 tagged.2

/-- Mapping the compact descriptors reconstructs the complete semantic route
list without loss of presentation order. -/
theorem constructedEdgeRoutes_eq_descriptorRoutes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    constructedEdgeRoutes graph =
      (routeDescriptors graph).map RouteDescriptor.route := by
  unfold constructedEdgeRoutes routeDescriptors
  rw [List.map_map]
  apply List.map_congr_left
  intro tagged _
  exact constructedEdgeRoute_eq_descriptorRoute graph tagged.1 tagged.2

/-- The indexed segment stream likewise factors through the compact numeric
route descriptors. -/
theorem drawing_indexedSegments_eq_descriptorSegments
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawing graph).indexedSegments =
      ((routeDescriptors graph).map RouteDescriptor.route).zipIdx.flatMap
        fun taggedRoute =>
          (gridPolylineSegments taggedRoute.1).zipIdx.map
            fun taggedSegment =>
              IndexedGridSegment.mk taggedRoute.2 taggedSegment.2
                taggedSegment.1 := by
  unfold PeriodicGridDrawing.indexedSegments drawing
  rw [constructedEdgeRoutes_eq_descriptorRoutes]

end PeriodicOrthocrossing
end LeanTrominoes

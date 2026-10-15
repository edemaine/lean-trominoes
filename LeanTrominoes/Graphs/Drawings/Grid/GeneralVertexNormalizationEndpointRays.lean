/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationFanAssignment
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointDirections

/-! # Lifted endpoint rays start at the corresponding prototype vertex -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

def endpointPort {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (target : Bool) : GraphPort Vertex :=
  if target then targetPort tagged.1 tagged.2 else sourcePort tagged.1 tagged.2

def endpointCell {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (target : Bool) : Cell :=
  if target then Cell.scale (-1) tagged.1.offset else (0,0)

theorem endpointPort_mem {Vertex : Type*} (graph : PeriodicGraph Vertex) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (target : Bool) : endpointPort tagged target ∈ allPorts graph := by
  cases target
  · exact sourcePort_mem_allPorts graph member
  · exact targetPort_mem_allPorts graph member

theorem endpoint_ray_contains {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target : Bool) :
    GridPolyline.RealContains (drawing.realEdgeRoute tagged.2 (endpointCell tagged target))
      (realHalfStep (drawing.vertexPosition graph (endpointPort tagged target).vertex)
        (portDirection drawing (endpointPort tagged target))) := by
  have routeMember := PeriodicGridDrawing.edgeRoute_mem_of_compatible valid.1 member
  have long := (valid.2.1 _ routeMember).1
  have routeOrthogonal := (PeriodicGridDrawing.isOrthogonal_iff_routes _).mp orthogonal _ routeMember
  have routeMatches := valid.1.2.2.2.2.2 tagged member
  cases target
  · change GridPolyline.RealContains
      (translatePolyline (drawing.periodTranslation (0,0)) (drawing.edgeRoute tagged.2))
      (realHalfStep (drawing.vertexPosition graph tagged.1.source)
        (AxisDirection.polylineFirstDirection (drawing.edgeRoute tagged.2)))
    rw [show drawing.periodTranslation (0,0) = (0,0) by simp [PeriodicGridDrawing.periodTranslation,Cell.scale],translatePolyline_zero]
    exact GridPolyline.realContains_halfStep_at_head long routeOrthogonal routeMatches.1
  · let shift := drawing.periodTranslation (Cell.scale (-1) tagged.1.offset)
    change GridPolyline.RealContains (translatePolyline shift (drawing.edgeRoute tagged.2))
      (realHalfStep (drawing.vertexPosition graph tagged.1.target)
        (AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2)).opposite)
    apply (GridPolyline.realContains_translate_inverse _ _ _).mpr
    have original := GridPolyline.realContains_halfStep_at_last_outward long routeOrthogonal routeMatches.2
    have pointEq :
        ((realHalfStep (drawing.vertexPosition graph tagged.1.target)
          (AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2)).opposite).1-shift.1,
          (realHalfStep (drawing.vertexPosition graph tagged.1.target)
            (AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2)).opposite).2-shift.2) =
        realHalfStep (Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset))
          (AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2)).opposite := by
      apply Prod.ext <;> simp [realHalfStep,shift,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add] <;> ring
    rw [pointEq]
    exact original

end LeanTrominoes.GeneralVertexNormalization

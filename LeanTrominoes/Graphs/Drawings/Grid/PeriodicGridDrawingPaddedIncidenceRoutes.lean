/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortJoins

/-! # The actual enlarged vertex fan routes used by the periodic assembler -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

def paddedIncidenceRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (port : GraphPort Vertex) : List Cell :=
  enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
    (drawing.vertexPosition graph port.vertex) (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)

theorem crossingBound_positive (drawing : PeriodicGridDrawing) : 0 < crossingBound drawing.gridSize := by
  have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
  unfold crossingBound
  positivity

theorem paddedIncidenceRoute_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (port : GraphPort Vertex) : (paddedIncidenceRoute graph drawing port).head? =
      some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph port.vertex)) :=
  enlargedRectangleTemplate_head ..

theorem paddedIncidenceRoute_last {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (paddedIncidenceRoute graph drawing port).getLast? =
      some (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph port.vertex))
        (Cell.scale (crossingBound drawing.gridSize) (portBoundaryAnchor graph drawing port))) := by
  have lookup : (vertexAnchorProfile graph drawing port.vertex).anchors[(incidenceAnchorIndex graph drawing port).val]? =
      some (portBoundaryAnchor graph drawing port) := by
    rw [← incidenceTemplate_last distinct degree member]
    exact incidenceTemplate_last_some distinct degree member
  exact enlargedRectangleTemplate_last_anchor _ _ _ _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member) lookup

theorem paddedIncidenceRoute_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (port : GraphPort Vertex) : GridPolyline.IsRealOpenSimple (paddedIncidenceRoute graph drawing port) :=
  enlargedRectangleTemplate_isRealOpenSimple _ (crossingBound_positive drawing) _ _ _

theorem paddedIncidenceRoute_orthogonal {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (port : GraphPort Vertex) : OrthogonalPolyline (paddedIncidenceRoute graph drawing port) :=
  enlargedRectangleTemplate_orthogonal _ (crossingBound_positive drawing) _ _ _

theorem paddedIncidenceRoutes_same_vertex_contact_center {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) {first last : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (lastMember : last ∈ allPorts graph)
    (sameVertex : first.vertex = last.vertex) (different : first ≠ last) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (paddedIncidenceRoute graph drawing first) point)
    (lastContains : GridPolyline.RealContains (paddedIncidenceRoute graph drawing last) point) :
    point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph first.vertex)) := by
  have lastValid := incidenceAnchorIndex_valid distinct degree lastMember
  rw [← sameVertex] at lastValid
  have indicesDifferent : incidenceAnchorIndex graph drawing first ≠ incidenceAnchorIndex graph drawing last :=
    fun equal => different (incidenceAnchorIndex_injective degree firstMember lastMember sameVertex equal)
  exact enlargedRectangleTemplate_contacts_center _ (crossingBound_positive drawing) _ _ _ _
    (vertexAnchorProfile_degree_le_four distinct degree _) (incidenceAnchorIndex_valid distinct degree firstMember) lastValid
    indicesDifferent firstContains (by simpa only [paddedIncidenceRoute,← sameVertex] using lastContains)

theorem rectangle_incidence_port_is_fan_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (right : Bool) {tagged : PeriodicEdge Vertex × Nat} {target : Bool}
    (valid : (RectanglePortKey.vertical right (.incidence tagged target)).Valid graph drawing column) :
    (paddedIncidenceRoute graph drawing (endpointPort tagged target)).getLast? =
      some (rectangleIntegralPortPoint graph drawing column (.vertical right (.incidence tagged target))) := by
  rw [rectangle_incidence_port_point planar degree straight column right valid]
  exact paddedIncidenceRoute_last (distinctPortRayKeys_of_planar_straight planar straight) degree (endpointPort_mem graph valid.1 target)

end LeanTrominoes.PeriodicGridDrawing

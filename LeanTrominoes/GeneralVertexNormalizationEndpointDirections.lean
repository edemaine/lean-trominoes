/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedTemplateJoints
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision
import LeanTrominoes.OrthogonalPolylineSymmetries

/-! # Uncolored endpoint directions of an arbitrary orthogonal periodic drawing -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

theorem firstDirection_genuine {route : List Cell} (long : 2 ≤ route.length)
    (orthogonal : OrthogonalPolyline route) : (AxisDirection.polylineFirstDirection route).IsGenuine := by
  cases route with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      exact AxisDirection.between_isGenuine_of_axisAligned (List.isChain_cons_cons.mp orthogonal).1

theorem lastDirection_genuine {route : List Cell} (long : 2 ≤ route.length)
    (orthogonal : OrthogonalPolyline route) : (AxisDirection.polylineLastDirection route).IsGenuine := by
  exact AxisDirection.opposite_isGenuine
    (firstDirection_genuine (by simpa using long) orthogonal.reverse)

def portDirection {Vertex : Type*} (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : AxisDirection :=
  match port.endKind with
  | .source => AxisDirection.polylineFirstDirection (drawing.edgeRoute port.edgeIndex)
  | .target => (AxisDirection.polylineLastDirection (drawing.edgeRoute port.edgeIndex)).opposite

def portSide {Vertex : Type*} (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : VertexSide :=
  VertexSide.ofDirection (portDirection drawing port)

theorem allPorts_has_edge {Vertex : Type*} {graph : PeriodicGraph Vertex} {port : GraphPort Vertex}
    (member : port ∈ allPorts graph) :
    ∃ tagged ∈ graph.edges.zipIdx, port = sourcePort tagged.1 tagged.2 ∨ port = targetPort tagged.1 tagged.2 := by
  obtain ⟨tagged,edgeMember,portMember⟩ := List.mem_flatMap.mp member
  simp only [edgePorts,List.mem_cons,List.not_mem_nil,or_false] at portMember
  exact ⟨tagged,edgeMember,portMember⟩

theorem portDirection_genuine {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) : (portDirection drawing port).IsGenuine := by
  obtain ⟨tagged,edgeMember,sourceOrTarget⟩ := allPorts_has_edge member
  have routeMember := PeriodicGridDrawing.edgeRoute_mem_of_compatible valid.1 edgeMember
  have long := (valid.2.1 _ routeMember).1
  have routeOrthogonal := (PeriodicGridDrawing.isOrthogonal_iff_routes _).mp orthogonal _ routeMember
  rcases sourceOrTarget with rfl | rfl
  · exact firstDirection_genuine long routeOrthogonal
  · exact AxisDirection.opposite_isGenuine (lastDirection_genuine long routeOrthogonal)

theorem portSide_direction {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (portSide drawing port).direction = portDirection drawing port :=
  VertexSide.direction_ofDirection _ (portDirection_genuine valid orthogonal member)

end LeanTrominoes.GeneralVertexNormalization

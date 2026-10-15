/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightAnchorAssignment
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorTemplateGeometry

/-! # Incidence order and isolated rectangle connector geometry -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem orderedIncidences_nodup {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) : (orderedIncidences graph drawing vertex).Nodup :=
  (orderedIncidences_perm graph drawing vertex).nodup_iff.mpr (portsAt_nodup graph vertex)

theorem orderedIncidences_strict {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (vertex : Vertex) :
    (orderedIncidences graph drawing vertex).Pairwise
      (fun first second => (drawing.portRayKey first).clockwiseCode < (drawing.portRayKey second).clockwiseCode) := by
  apply ((orderedIncidences_ordered graph drawing vertex).and (orderedIncidences_nodup graph drawing vertex)).imp_of_mem
  intro first second firstMember secondMember both
  have firstData := (orderedIncidences_mem graph drawing vertex first).mp firstMember
  have secondData := (orderedIncidences_mem graph drawing vertex second).mp secondMember
  exact lt_of_le_of_ne both.1 (fun equal => both.2
    (distinct first firstData.1 second secondData.1 (firstData.2.trans secondData.2.symm)
      (StraightRayKey.clockwiseCode_injective equal)))

theorem rectangleTemplate_firstDirection_injective (profile : AnchorProfile) (degree : profile.degree ≤ 4)
    {first second : Fin 4} (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (equal : AxisDirection.polylineFirstDirection (rectangleTemplate profile first) =
      AxisDirection.polylineFirstDirection (rectangleTemplate profile second)) : first = second := by
  have distinct := profile.initialDirections_nodup degree
  exact List.inj_on_of_nodup_map distinct
    (by simp [firstValid]) (by simp [secondValid]) equal

theorem incidenceTemplate_firstDirection_injective {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex)
    (equal : AxisDirection.polylineFirstDirection (incidenceTemplate graph drawing first) =
      AxisDirection.polylineFirstDirection (incidenceTemplate graph drawing second)) : first = second := by
  have secondValid := incidenceAnchorIndex_valid distinct degree secondMember
  rw [← sameVertex] at secondValid
  have secondEq : incidenceTemplate graph drawing second = rectangleTemplate
      (vertexAnchorProfile graph drawing first.vertex) (incidenceAnchorIndex graph drawing second) := by
    simp only [incidenceTemplate,sameVertex]
  rw [secondEq] at equal
  exact incidenceAnchorIndex_injective degree firstMember secondMember sameVertex
    (rectangleTemplate_firstDirection_injective _ (vertexAnchorProfile_degree_le_four distinct degree _)
      (incidenceAnchorIndex_valid distinct degree firstMember) secondValid equal)

theorem vertexAnchorDirections_clockwise {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) (vertex : Vertex) :
    ClockwiseDirections (vertexAnchorProfile graph drawing vertex).initialDirections :=
  AnchorProfile.initialDirections_clockwise _ (vertexAnchorProfile_degree_le_four distinct degree vertex)

theorem incidenceTemplate_boundary_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (side : VertexSide)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (incidenceTemplate graph drawing port) point)
    (boundary : GridPolyline.RealContains (rectangleBoundaryRoute side) point) :
    point = realCell ((incidenceTemplate graph drawing port).getLast?.getD (0,0)) :=
  rectangleTemplate_boundary_contact _ _ side (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member) contains boundary

def incidenceTemplateAt {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (factor : Int) (port : GraphPort Vertex) (position : Cell) : List Cell :=
  rectangleTemplateAt factor position (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)

theorem incidenceTemplateAt_avoids_nonincident_segment {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) {grid factor : Int}
    (gridPositive : 0 < grid) (large : 30*grid+10 < factor) (port : GraphPort Vertex) (position : Cell)
    {segment : GridSegment} (width : |segment.finish.1-segment.start.1| ≤ 2*grid)
    (height : |segment.finish.2-segment.start.2| ≤ 2*grid) (avoids : ¬segment.RealContains (realCell position))
    {point : ℝ × ℝ} (templateContains : GridPolyline.RealContains (incidenceTemplateAt graph drawing factor port position) point)
    (segmentContains : (segment.scale factor).RealContains point) : False :=
  rectangleTemplateAt_avoids_nonincident_segment gridPositive.le large width height avoids _ _ templateContains segmentContains

end LeanTrominoes.OrthogonalDrawingRefinement

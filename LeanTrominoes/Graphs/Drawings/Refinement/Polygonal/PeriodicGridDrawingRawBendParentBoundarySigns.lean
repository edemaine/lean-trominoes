/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentRayGeometry

/-! # Actual parent-route geometry gives the inward signs at boundary bends -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem bendCenter_point {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) :
    bendCenter source drawing edgeIndex pointIndex = (drawing.edgeRoute edgeIndex).getD pointIndex (0,0) :=
  representative_lift _ _

theorem bendCenter_inside_parent_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {edgeIndex pointIndex : Nat} (parentIndex : parent.2 = edgeIndex)
    (vertexMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    drawing.PointInLocalRectangle parent.1.offset (bendCenter source drawing edgeIndex pointIndex) := by
  have pointBounds := bend_vertex_mem_bounds planar.1.1 vertexMember
  have pointValid : pointIndex < (drawing.edgeRoute edgeIndex).length := by omega
  have member : (drawing.edgeRoute edgeIndex).getD pointIndex (0,0) ∈ drawing.edgeRoute edgeIndex := by
    rw [List.getD_eq_getElem _ _ pointValid]
    exact List.getElem_mem pointValid
  rw [← parentIndex] at member
  rw [bendCenter_point,← parentIndex]
  exact polygonal_point_in_local_rectangle drawingLocal parentMember
    (planar.1.2.1 _ (edgeRoute_mem_of_compatible planar.1.1 parentMember)).1 member

theorem bend_port_parent_boundary_signs {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {port : GraphPort (Vertex V)} (portMember : port ∈ allPorts (subdivisionGraph source drawing))
    {edgeIndex pointIndex : Nat} (parentIndex : parent.2 = edgeIndex) (vertex : port.vertex = .bend edgeIndex pointIndex) :
    ((bendCenter source drawing edgeIndex pointIndex).1 = min 0 ((drawing.gridSize : Int)*parent.1.offset.1) →
      0 ≤ BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey port)) ∧
    ((bendCenter source drawing edgeIndex pointIndex).1 = (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.1) →
      BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey port) ≤ 0) ∧
    ((bendCenter source drawing edgeIndex pointIndex).2 = min 0 ((drawing.gridSize : Int)*parent.1.offset.2) →
      0 ≤ BendFan.verticalSign ((shiftedDrawing source drawing).portRayKey port)) ∧
    ((bendCenter source drawing edgeIndex pointIndex).2 = (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.2) →
      BendFan.verticalSign ((shiftedDrawing source drawing).portRayKey port) ≤ 0) := by
  obtain ⟨segment,key,start,finishMember,genuine⟩ := bend_port_outward_segment planar portMember vertex
  rw [← parentIndex] at finishMember
  have bounds := polygonal_point_in_local_rectangle drawingLocal parentMember
    (planar.1.2.1 _ (edgeRoute_mem_of_compatible planar.1.1 parentMember)).1 finishMember
  simp only [PointInLocalRectangle] at bounds
  rw [key]
  refine ⟨?_,?_,?_,?_⟩
  · intro boundary
    apply BendFan.segment_horizontalSign_nonnegative
    simp only [GridSegment.direction,start]
    omega
  · intro boundary
    apply BendFan.segment_horizontalSign_nonpositive
    simp only [GridSegment.direction,start]
    omega
  · intro boundary
    apply BendFan.segment_verticalSign_nonnegative genuine
    simp only [GridSegment.direction,start]
    omega
  · intro boundary
    apply BendFan.segment_verticalSign_nonpositive
    simp only [GridSegment.direction,start]
    omega

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPeriodicVerticalPorts
import LeanTrominoes.PeriodicGridDrawingColumnPortTransport

/-! # Column-port transport includes the fundamental square's boundary columns -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem crossing_copy_row_zero {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Int} {key : Nat × Cell} (member : key ∈ verticalCrossingCopies graph drawing column) :
    rationalCell drawing.gridSize ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column) = 0 := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  exact rationalCell_of_in_cell positive (of_decide_eq_true (List.mem_filter.mp member).2).2

theorem paddedVerticalSlabPort_eq_finite {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (member : key ∈ verticalCrossingCopies graph drawing column) (right : Bool) :
    paddedVerticalSlabPort graph drawing column ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column) 0 right =
      finiteVerticalSlabPort graph drawing column key right := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have bounds := (of_decide_eq_true (List.mem_filter.mp member).2).2
  have modulo : (column : Int) % drawing.gridSize = column := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast columnBound)
  simp only [paddedVerticalSlabPort,finiteVerticalSlabPort,mul_zero,sub_zero,paddedPeriodicColumnHeight,modulo]
  rw [periodicRedistributedHeight_in_cell positive _ _ bounds]

def ColumnPortKey.periodicIntegralPort {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : ColumnPortKey Vertex → OrthogonalBoundaryRouting.Port
  | .crossing key => paddedVerticalSlabPort graph drawing column
      ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column) 0 right
  | .incidence tagged target => assignedFanSlabPort graph drawing tagged target right

theorem finite_copy_vertical_port_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Int} {first second : Nat × Cell} (firstMember : first ∈ verticalCrossingCopies graph drawing column)
    (secondMember : second ∈ verticalCrossingCopies graph drawing column) (right : Bool)
    (ordered : (virtualVerticalPort graph drawing column first right).coordinate <
      (virtualVerticalPort graph drawing column second right).coordinate) :
    (paddedVerticalSlabPort graph drawing column ((drawing.liftedStraightSegment first.1 first.2).rationalLineHeight column) 0 right).coordinate <
      (paddedVerticalSlabPort graph drawing column ((drawing.liftedStraightSegment second.1 second.2).rationalLineHeight column) 0 right).coordinate := by
  obtain ⟨firstTagged,firstAt,firstIndex,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp firstMember).1
  obtain ⟨secondTagged,secondAt,secondIndex,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp secondMember).1
  have firstCrosses := (of_decide_eq_true (List.mem_filter.mp firstMember).2).1
  have secondCrosses := (of_decide_eq_true (List.mem_filter.mp secondMember).2).1
  rw [← firstIndex] at firstCrosses
  rw [← secondIndex] at secondCrosses
  have sameRow : rationalCell drawing.gridSize ((drawing.liftedStraightSegment firstTagged.2 first.2).rationalLineHeight column) =
      rationalCell drawing.gridSize ((drawing.liftedStraightSegment secondTagged.2 second.2).rationalLineHeight column) := by
    rw [firstIndex,secondIndex,crossing_copy_row_zero firstMember,crossing_copy_row_zero secondMember]
  exact periodicVerticalPort_coordinate_order planar degree straight firstAt secondAt
    (graphLocal _ (List.fst_mem_of_mem_zipIdx firstAt)) (graphLocal _ (List.fst_mem_of_mem_zipIdx secondAt))
    first.2 second.2 firstCrosses secondCrosses sameRow 0 right
    (by simpa only [firstIndex,secondIndex,periodicVirtualVerticalPort,virtualVerticalPort,Int.cast_zero,mul_zero,sub_zero,Prod.eta] using ordered)
    |> fun result => by simpa only [firstIndex,secondIndex] using result

theorem periodic_columnPort_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (right : Bool) {first second : ColumnPortKey Vertex}
    (firstValid : first.Valid graph drawing column right) (secondValid : second.Valid graph drawing column right)
    (ordered : (first.virtualPort graph drawing column right).coordinate < (second.virtualPort graph drawing column right).coordinate) :
    (first.periodicIntegralPort graph drawing column right).coordinate < (second.periodicIntegralPort graph drawing column right).coordinate := by
  cases first with
  | crossing first =>
    cases second with
    | crossing second => exact finite_copy_vertical_port_coordinate_order planar degree graphLocal straight firstValid secondValid right ordered
    | incidence tagged target =>
      have bounds := outwardStraightSegment_start_bounds planar.1.1 secondValid.1 target
      have sameX := secondValid.2.1
      have columnBound : column < drawing.gridSize := by
        have upper := bounds.2.1
        rw [sameX] at upper
        exact_mod_cast upper
      have mapped := columnPort_coordinate_order planar degree straight columnBound right firstValid secondValid ordered
      simpa only [ColumnPortKey.periodicIntegralPort,ColumnPortKey.integralPort,paddedVerticalSlabPort_eq_finite columnBound firstValid] using mapped
  | incidence tagged target =>
    have bounds := outwardStraightSegment_start_bounds planar.1.1 firstValid.1 target
    have sameX := firstValid.2.1
    have columnBound : column < drawing.gridSize := by
      have upper := bounds.2.1
      rw [sameX] at upper
      exact_mod_cast upper
    cases second with
    | crossing key =>
      have mapped := columnPort_coordinate_order planar degree straight columnBound right firstValid secondValid ordered
      simpa only [ColumnPortKey.periodicIntegralPort,ColumnPortKey.integralPort,paddedVerticalSlabPort_eq_finite columnBound secondValid] using mapped
    | incidence second secondTarget =>
      exact columnPort_coordinate_order planar degree straight columnBound right firstValid secondValid ordered

theorem periodic_columnPort_virtual_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Int) (right : Bool) {key : ColumnPortKey Vertex} (valid : key.Valid graph drawing column right) :
    (key.virtualPort graph drawing column right).Inside ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  cases key with
  | crossing key =>
    obtain ⟨tagged,member,index,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp valid).1
    have crosses := (of_decide_eq_true (List.mem_filter.mp valid).2).1
    rw [← index] at crosses
    have inside := periodicVirtualVerticalPort_inside planar straight member (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) key.2 crosses right
    dsimp only at inside
    simpa only [index,crossing_copy_row_zero valid,periodicVirtualVerticalPort,ColumnPortKey.virtualPort,virtualVerticalPort,Int.cast_zero,mul_zero,sub_zero,Prod.eta] using inside
  | incidence tagged target => exact virtualIncidencePort_inside planar straight valid.1 target right

theorem periodic_columnPort_integral_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Int) (right : Bool) {key : ColumnPortKey Vertex} (valid : key.Valid graph drawing column right) :
    (key.periodicIntegralPort graph drawing column right).Inside drawing.paddedSlabWidth
      (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  cases key with
  | crossing key =>
    obtain ⟨tagged,member,index,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp valid).1
    have crosses := (of_decide_eq_true (List.mem_filter.mp valid).2).1
    rw [← index] at crosses
    have inside := paddedVerticalSlabPort_inside planar.1.1 degree member (straight tagged member)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) key.2 crosses right
    dsimp only at inside
    simpa only [index,crossing_copy_row_zero valid,ColumnPortKey.periodicIntegralPort] using inside
  | incidence tagged target => exact columnPort_integral_inside planar degree straight column right valid

end LeanTrominoes.PeriodicGridDrawing

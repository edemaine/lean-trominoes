/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVirtualVerticalPortOrder

/-! # Column crossing redistribution preserves order beside enlarged vertex fans -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement RationalPerturbation GeneralVertexNormalization PeriodicOrthocrossing

theorem outwardStraightSegment_start_mem {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (target : Bool) :
    (drawing.outwardStraightSegment tagged target).start ∈ drawing.vertexPositions := by
  rw [outwardStraightSegment_start compatible member target]
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  apply compatible.vertexPosition_mem
  cases target
  · simpa [endpointPort,sourcePort] using endpoints.1
  · simpa [endpointPort,targetPort] using endpoints.2

theorem finiteCrossingHeight_ne_incidence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Int} {key : Nat × Cell} (crossingMember : key ∈ verticalCrossingCopies graph drawing column)
    {tagged : PeriodicEdge Vertex × Nat} (incidenceMember : tagged ∈ graph.edges.zipIdx) (target : Bool)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1 = column) :
    (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column ≠
      ((drawing.outwardStraightSegment tagged target).start.2 : ℚ) := by
  obtain ⟨crossing,crossingAt,index,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp crossingMember).1
  have crosses := (of_decide_eq_true (List.mem_filter.mp crossingMember).2).1
  rw [← index] at crosses ⊢
  exact verticalCrossingHeight_ne_vertex valid crossingAt (straight crossing crossingAt) key.2 crosses
    (outwardStraightSegment_start_mem valid.1 incidenceMember target) sameX

theorem perturbedCrossing_lt_incidence_iff {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (crossingMember : key ∈ verticalCrossingCopies graph drawing column)
    {tagged : PeriodicEdge Vertex × Nat} (incidenceMember : tagged ∈ graph.edges.zipIdx) (target right : Bool)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1 = column) :
    perturbedColumnHeight graph drawing column key right < perturbedIncidenceHeight graph drawing tagged target right ↔
      (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column <
        ((drawing.outwardStraightSegment tagged target).start.2 : ℚ) := by
  rw [perturbedColumnHeight_eq_evaluate,perturbedIncidenceHeight_eq_evaluate,
    columnPerturbation_order_iff planar straight (mem_columnPerturbationValues_crossing columnBound crossingMember right)
      (mem_columnPerturbationValues_incidence (drawing := drawing) incidenceMember target right)]
  have different := finiteCrossingHeight_ne_incidence planar.1 straight crossingMember incidenceMember target sameX
  simp only [RationalPerturbation.Before,Prod.fst,Prod.snd,different,false_and,or_false]

theorem perturbedIncidence_lt_crossing_iff {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (crossingMember : key ∈ verticalCrossingCopies graph drawing column)
    {tagged : PeriodicEdge Vertex × Nat} (incidenceMember : tagged ∈ graph.edges.zipIdx) (target right : Bool)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1 = column) :
    perturbedIncidenceHeight graph drawing tagged target right < perturbedColumnHeight graph drawing column key right ↔
      ((drawing.outwardStraightSegment tagged target).start.2 : ℚ) <
        (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column := by
  rw [perturbedColumnHeight_eq_evaluate,perturbedIncidenceHeight_eq_evaluate,
    columnPerturbation_order_iff planar straight
      (mem_columnPerturbationValues_incidence (drawing := drawing) incidenceMember target right)
      (mem_columnPerturbationValues_crossing columnBound crossingMember right)]
  have different := (finiteCrossingHeight_ne_incidence planar.1 straight crossingMember incidenceMember target sameX).symm
  simp only [RationalPerturbation.Before,Prod.fst,Prod.snd,different,false_and,or_false]

theorem crossing_fan_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (crossingMember : key ∈ verticalCrossingCopies graph drawing column)
    {tagged : PeriodicEdge Vertex × Nat} (incidenceMember : tagged ∈ graph.edges.zipIdx) (target right : Bool)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1 = column) {anchor : Cell}
    (anchorBounds : -10 ≤ anchor.2 ∧ anchor.2 ≤ 10)
    (ordered : (virtualVerticalPort graph drawing column key right).coordinate <
      (virtualIncidencePort graph drawing tagged target right).coordinate) :
    (finiteVerticalSlabPort graph drawing column key right).coordinate <
      (drawing.paddedFanSlabPort (drawing.outwardStraightSegment tagged target).start anchor right).coordinate := by
  have realOrder : (perturbedColumnHeight graph drawing column key right : ℝ) <
      (perturbedIncidenceHeight graph drawing tagged target right : ℝ) := by
    dsimp only [virtualVerticalPort,virtualIncidencePort] at ordered
    linarith
  have oldOrder := (perturbedCrossing_lt_incidence_iff planar straight columnBound crossingMember incidenceMember target right sameX).mp
    (by exact_mod_cast realOrder)
  have heightMember : (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column ∈ verticalCrossingHeights graph drawing column :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,crossingMember,rfl⟩)
  have gap := paddedCrossingHeight_below_vertex planar.1.1 degree heightMember
    (outwardStraightSegment_start_mem planar.1.1 incidenceMember target) sameX oldOrder
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have lower := mul_le_mul_of_nonneg_left anchorBounds.1 nonnegative
  dsimp only [finiteVerticalSlabPort,paddedFanSlabPort]
  nlinarith

theorem fan_crossing_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) {key : Nat × Cell}
    (crossingMember : key ∈ verticalCrossingCopies graph drawing column)
    {tagged : PeriodicEdge Vertex × Nat} (incidenceMember : tagged ∈ graph.edges.zipIdx) (target right : Bool)
    (sameX : (drawing.outwardStraightSegment tagged target).start.1 = column) {anchor : Cell}
    (anchorBounds : -10 ≤ anchor.2 ∧ anchor.2 ≤ 10)
    (ordered : (virtualIncidencePort graph drawing tagged target right).coordinate <
      (virtualVerticalPort graph drawing column key right).coordinate) :
    (drawing.paddedFanSlabPort (drawing.outwardStraightSegment tagged target).start anchor right).coordinate <
      (finiteVerticalSlabPort graph drawing column key right).coordinate := by
  have realOrder : (perturbedIncidenceHeight graph drawing tagged target right : ℝ) <
      (perturbedColumnHeight graph drawing column key right : ℝ) := by
    dsimp only [virtualVerticalPort,virtualIncidencePort] at ordered
    linarith
  have oldOrder := (perturbedIncidence_lt_crossing_iff planar straight columnBound crossingMember incidenceMember target right sameX).mp
    (by exact_mod_cast realOrder)
  have heightMember : (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column ∈ verticalCrossingHeights graph drawing column :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,crossingMember,rfl⟩)
  have gap := paddedCrossingHeight_above_vertex planar.1.1 degree heightMember
    (outwardStraightSegment_start_mem planar.1.1 incidenceMember target) sameX oldOrder.le
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have upper := mul_le_mul_of_nonneg_left anchorBounds.2 nonnegative
  dsimp only [finiteVerticalSlabPort,paddedFanSlabPort]
  nlinarith

end LeanTrominoes.PeriodicGridDrawing

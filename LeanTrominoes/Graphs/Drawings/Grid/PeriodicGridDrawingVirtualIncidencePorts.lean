/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingColumnPerturbationGeometry
import LeanTrominoes.Common.Geometry.GridSegmentRationalOutwardColumnCut
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingAnchorBoundaryOrder
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedFanPorts

/-! # Proper virtual rectangle ports for nonvertical vertex incidences -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalPerturbation RealRectangleBoundary GeneralVertexNormalization PeriodicOrthocrossing

theorem outwardStraightSegment_start_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (target : Bool) :
    drawing.PositionInFundamentalSquare (drawing.outwardStraightSegment tagged target).start := by
  rw [outwardStraightSegment_start compatible member target]
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  apply compatible.2.2.2.2.1
  apply compatible.vertexPosition_mem
  cases target
  · simpa [endpointPort,sourcePort] using endpoints.1
  · simpa [endpointPort,targetPort] using endpoints.2

def perturbedIncidenceHeight {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target left : Bool) : ℚ :=
  (drawing.outwardStraightSegment tagged target).rationalHeightAt
    (((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+
      (if left then -columnPerturbation graph drawing else columnPerturbation graph drawing))

theorem perturbedIncidenceHeight_eq_evaluate {Vertex : Type*} (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) (target left : Bool) :
    perturbedIncidenceHeight graph drawing tagged target left = evaluate (columnPerturbation graph drawing)
      (((drawing.outwardStraightSegment tagged target).start.2 : ℚ),
        if left then -(drawing.outwardStraightSegment tagged target).rationalSlope else
          (drawing.outwardStraightSegment tagged target).rationalSlope) := by
  unfold perturbedIncidenceHeight
  rw [GridSegment.rationalHeightAt_start_add]
  cases left <;> simp [evaluate] <;> ring

theorem perturbedIncidenceHeight_in_row {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) :
    -seamPerturbation graph drawing < perturbedIncidenceHeight graph drawing tagged target left ∧
      perturbedIncidenceHeight graph drawing tagged target left < (drawing.gridSize : ℚ)-seamPerturbation graph drawing := by
  have bounds := outwardStraightSegment_start_bounds planar.1.1 member target
  unfold PositionInFundamentalSquare at bounds
  have shiftPositive := seamPerturbation_positive graph drawing
  have shiftSmall := seamPerturbation_lt_one graph drawing
  have lower : (0 : ℚ) < (drawing.outwardStraightSegment tagged target).start.2 := by exact_mod_cast bounds.2.2.1
  have upper : ((drawing.outwardStraightSegment tagged target).start.2 : ℚ)+1 ≤ drawing.gridSize := by
    exact_mod_cast (by omega : (drawing.outwardStraightSegment tagged target).start.2+1 ≤ drawing.gridSize)
  have pointMember := mem_columnPerturbationValues_incidence (drawing := drawing) member target left
  have rows := mem_columnPerturbationValues_rows graph drawing
  have lo := columnPerturbation_preserves_order planar straight rows.1 pointMember (Or.inl (by linarith))
  have hi := columnPerturbation_preserves_order planar straight pointMember rows.2 (Or.inl (by linarith))
  rw [perturbedIncidenceHeight_eq_evaluate]
  constructor
  · simpa only [evaluate,Prod.fst,Prod.snd,mul_zero,add_zero] using lo
  · simpa only [evaluate,Prod.fst,Prod.snd,mul_zero,add_zero] using hi

theorem perturbedIncidenceHeight_realInteriorContains {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat) (target left : Bool)
    (direction : if left then (drawing.outwardStraightSegment tagged target).finish.1 <
        (drawing.outwardStraightSegment tagged target).start.1 else
      (drawing.outwardStraightSegment tagged target).start.1 < (drawing.outwardStraightSegment tagged target).finish.1) :
    (drawing.outwardStraightSegment tagged target).RealInteriorContains
      ((((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+
        (if left then -columnPerturbation graph drawing else columnPerturbation graph drawing) : ℝ),
        (perturbedIncidenceHeight graph drawing tagged target left : ℝ)) := by
  have small : columnPerturbation graph drawing < 1 :=
    lt_trans ((columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)) (by norm_num)
  cases left
  · simpa [perturbedIncidenceHeight] using
      GridSegment.outward_column_cut_realInteriorContains (columnPerturbation_positive planar straight) small true direction
  · simpa [perturbedIncidenceHeight] using
      GridSegment.outward_column_cut_realInteriorContains (columnPerturbation_positive planar straight) small false direction

def virtualIncidencePort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target left : Bool) : Port :=
  ⟨if left then 2 else 0,((perturbedIncidenceHeight graph drawing tagged target left+seamPerturbation graph drawing) : ℝ)⟩

theorem virtualIncidencePort_inside {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) :
    (virtualIncidencePort graph drawing tagged target left).Inside
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have bounds := perturbedIncidenceHeight_in_row planar straight member target left
  have lo : (0 : ℚ) < perturbedIncidenceHeight graph drawing tagged target left+seamPerturbation graph drawing := by linarith
  have hi : perturbedIncidenceHeight graph drawing tagged target left+seamPerturbation graph drawing < (drawing.gridSize : ℚ) := by linarith
  have realBounds : (0 : ℝ) < ((perturbedIncidenceHeight graph drawing tagged target left+seamPerturbation graph drawing) : ℝ) ∧
      ((perturbedIncidenceHeight graph drawing tagged target left+seamPerturbation graph drawing) : ℝ) < (drawing.gridSize : ℝ) :=
    ⟨by exact_mod_cast lo,by exact_mod_cast hi⟩
  cases left <;> simpa [virtualIncidencePort,Port.Inside,Port.extent] using realBounds

theorem virtualIncidencePort_point {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool) :
    (virtualIncidencePort graph drawing tagged target left).shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing)
        ((drawing.vertexPosition graph (endpointPort tagged target).vertex).1-if left then 1 else 0) 0)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) =
    ((((drawing.outwardStraightSegment tagged target).start.1 : ℚ)+
      (if left then -columnPerturbation graph drawing else columnPerturbation graph drawing) : ℝ),
      (perturbedIncidenceHeight graph drawing tagged target left : ℝ)) := by
  rw [outwardStraightSegment_start compatible member target]
  cases left <;> apply Prod.ext <;>
    simp [virtualIncidencePort,virtualSlabOrigin,Port.shiftedPoint,Port.point] <;> ring

theorem virtualIncidencePort_realInteriorContains {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target left : Bool)
    (direction : if left then (drawing.outwardStraightSegment tagged target).finish.1 <
        (drawing.outwardStraightSegment tagged target).start.1 else
      (drawing.outwardStraightSegment tagged target).start.1 < (drawing.outwardStraightSegment tagged target).finish.1) :
    (drawing.outwardStraightSegment tagged target).RealInteriorContains
      ((virtualIncidencePort graph drawing tagged target left).shiftedPoint
        (virtualSlabOrigin graph drawing (columnPerturbation graph drawing)
          ((drawing.vertexPosition graph (endpointPort tagged target).vertex).1-if left then 1 else 0) 0)
        ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ)) := by
  rw [virtualIncidencePort_point planar.1.1 member target left]
  exact perturbedIncidenceHeight_realInteriorContains planar straight tagged target left direction

end LeanTrominoes.PeriodicGridDrawing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCutCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingHorizontalCutCoverage
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalRectangleBoundaryPoints
import LeanTrominoes.Common.Geometry.GridSegmentRationalHeightContact

/-! # Computed rectangle ports are exact rational affine boundary contacts -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

def RectanglePortKey.rationalPoint {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) : ℚ × ℚ :=
  boundaryPoint (1-2*columnPerturbation graph drawing) drawing.gridSize
    (key.rationalCoordinate graph drawing column) key.side

def rectangleAffineBase {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) : ℚ :=
  (drawing.liftedStraightSegment parent.1 parent.2).rationalHeightAt ((column : ℚ)+columnPerturbation graph drawing)+
    seamPerturbation graph drawing

theorem rectangle_affine_height {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (coordinate : ℚ) :
    rectangleAffineBase graph drawing column parent+(drawing.liftedStraightSegment parent.1 parent.2).rationalSlope*coordinate =
      (drawing.liftedStraightSegment parent.1 parent.2).rationalHeightAt
        ((column : ℚ)+columnPerturbation graph drawing+coordinate)+seamPerturbation graph drawing := by
  rw [GridSegment.rationalHeightAt_add]
  unfold rectangleAffineBase
  ring

theorem rectanglePort_rationalPoint_shifted {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) :
    ((((column : ℚ)+columnPerturbation graph drawing+(key.rationalPoint graph drawing column).1 : ℚ) : ℝ),
      ((-seamPerturbation graph drawing+(key.rationalPoint graph drawing column).2 : ℚ) : ℝ)) =
      (key.virtualPort graph drawing column).shiftedPoint
        (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
        ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have portEqual : RealRectangleBoundary.Port.mk key.side (key.rationalCoordinate graph drawing column : ℝ) =
      key.virtualPort graph drawing column := by
    apply RealRectangleBoundary.Port.clockwiseCode_injective
    simp only [RealRectangleBoundary.Port.clockwiseCode]
    rw [rectanglePort_virtual_side,rectanglePort_virtual_coordinate]
  have pointEqual := boundaryPoint_cast (1-2*columnPerturbation graph drawing) drawing.gridSize
    (key.rationalCoordinate graph drawing column) key.side
  rw [portEqual] at pointEqual
  change (((key.rationalPoint graph drawing column).1 : ℝ),((key.rationalPoint graph drawing column).2 : ℝ)) = _ at pointEqual
  have hx := congrArg Prod.fst pointEqual
  have hy := congrArg Prod.snd pointEqual
  dsimp only at hx hy
  simp only [Rat.cast_natCast] at hx hy
  apply Prod.ext <;>
    simp only [RealRectangleBoundary.Port.shiftedPoint,virtualSlabOrigin,Rat.cast_add,Rat.cast_neg,
      Rat.cast_natCast,Rat.cast_intCast,Int.cast_zero,mul_zero,zero_sub]
  · exact congrArg (fun value => (column : ℝ)+(columnPerturbation graph drawing : ℝ)+value) hx
  · simpa only [add_comm] using congrArg (fun value => -(seamPerturbation graph drawing : ℝ)+value) hy

theorem rectanglePort_rational_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    Contact (1-2*columnPerturbation graph drawing) drawing.gridSize
      (rectangleAffineBase graph drawing column key.parentKey)
      (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).rationalSlope
      (key.rationalPoint graph drawing column) := by
  have inside := rectanglePort_virtual_inside planar graphLocal straight column valid
  have rationalInside : (RealRectangleBoundary.Port.mk key.side (key.rationalCoordinate graph drawing column : ℝ)).Inside
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) ((drawing.gridSize : ℚ) : ℝ) := by
    simpa only [← rectanglePort_virtual_side graph drawing column key,← rectanglePort_virtual_coordinate graph drawing column key,Rat.cast_natCast] using inside
  have boundary := boundaryPoint_on_boundary key.side rationalInside
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have xBounds := boundaryPoint_x_bounds widthPositive key.side rationalInside
  have between := GridSegment.unit_column_inner_coordinate_between
    (rectanglePort_parent_spans_unit_column planar graphLocal straight column valid) (columnPerturbation_positive planar straight) xBounds
  have actual := GridSegment.realInteriorContains_implies_realContains (rectanglePort_parent_realInteriorContains planar straight column valid)
  rw [← rectanglePort_rationalPoint_shifted] at actual
  have heightEqual := GridSegment.rationalHeightAt_eq_of_realContains
    (by simpa only [Int.cast_natCast,RectanglePortKey.rationalPoint] using between) actual
  refine ⟨?_,boundary⟩
  rw [rectangle_affine_height,heightEqual]
  ring

end LeanTrominoes.PeriodicGridDrawing

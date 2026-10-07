/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVirtualSlabCuts
import LeanTrominoes.RealRectangleBoundaryShiftedNoninterlacing

/-! # Actual straight-chord ports on the rationally shifted row boundaries -/
namespace LeanTrominoes.PeriodicGridDrawing
open RealRectangleBoundary

def virtualSlabOrigin {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (epsilon : ℚ) (column row : Int) : ℝ × ℝ :=
  (((column : ℚ)+epsilon : ℝ),((drawing.gridSize : ℚ)*row-seamPerturbation graph drawing : ℝ))

def virtualHorizontalPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (epsilon : ℚ) (key : Nat × Cell) (top : Bool) : Port :=
  ⟨if top then 1 else 3,((shiftedSeamAbscissa graph drawing key-(seamAssignedSlab graph drawing key : ℚ)-epsilon) : ℝ)⟩

theorem virtualSlabWidth_positive {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {epsilon : ℚ} (small : epsilon ≤ columnCutMargin graph drawing) : 0 < (1-2*epsilon : ℚ) := by
  have bound := columnCutMargin_lt_half graph drawing
  linarith

theorem virtualHorizontalPort_inside {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {epsilon : ℚ} (positive : 0 < epsilon) (small : epsilon ≤ columnCutMargin graph drawing)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) (top : Bool) :
    (virtualHorizontalPort graph drawing epsilon key top).Inside ((1-2*epsilon : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have bounds := shiftedSeamAbscissa_inside_shrunken_slab planar straight positive small member
  have lo : (0 : ℚ) < shiftedSeamAbscissa graph drawing key-(seamAssignedSlab graph drawing key : ℚ)-epsilon := by linarith
  have hi : shiftedSeamAbscissa graph drawing key-(seamAssignedSlab graph drawing key : ℚ)-epsilon < 1-2*epsilon := by linarith
  have realBounds : (0 : ℝ) < ((shiftedSeamAbscissa graph drawing key-(seamAssignedSlab graph drawing key : ℚ)-epsilon) : ℝ) ∧
      ((shiftedSeamAbscissa graph drawing key-(seamAssignedSlab graph drawing key : ℚ)-epsilon) : ℝ) < ((1-2*epsilon : ℚ) : ℝ) :=
    ⟨by exact_mod_cast lo,by exact_mod_cast hi⟩
  cases top <;> simpa [virtualHorizontalPort,Port.Inside,Port.extent] using realBounds

theorem virtualHorizontalPort_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (epsilon : ℚ) (key : Nat × Cell) (top : Bool) :
    (virtualHorizontalPort graph drawing epsilon key top).shiftedPoint
      (virtualSlabOrigin graph drawing epsilon (seamAssignedSlab graph drawing key) (if top then -1 else 0))
      ((1-2*epsilon : ℚ) : ℝ) (drawing.gridSize : ℝ) =
        ((shiftedSeamAbscissa graph drawing key : ℝ),((-seamPerturbation graph drawing : ℚ) : ℝ)) := by
  cases top <;> apply Prod.ext <;>
    simp [virtualHorizontalPort,virtualSlabOrigin,Port.shiftedPoint,Port.point] <;> ring

theorem virtualHorizontalPort_realInteriorContains {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) (epsilon : ℚ) (top : Bool) :
    (drawing.liftedStraightSegment key.1 key.2).RealInteriorContains
      ((virtualHorizontalPort graph drawing epsilon key top).shiftedPoint
        (virtualSlabOrigin graph drawing epsilon (seamAssignedSlab graph drawing key) (if top then -1 else 0))
        ((1-2*epsilon : ℚ) : ℝ) (drawing.gridSize : ℝ)) := by
  have horizontalMember := (List.mem_filter.mp member).1
  have crosses := (of_decide_eq_true (List.mem_filter.mp horizontalMember).2).1
  have actual := GridSegment.shifted_horizontal_seam_realInteriorContains crosses
    (seamPerturbation_positive graph drawing) (seamPerturbation_lt_one graph drawing)
  rw [virtualHorizontalPort_point]
  simpa only [Int.cast_zero,Rat.cast_zero,zero_sub,Rat.cast_neg,shiftedSeamAbscissa] using actual

end LeanTrominoes.PeriodicGridDrawing

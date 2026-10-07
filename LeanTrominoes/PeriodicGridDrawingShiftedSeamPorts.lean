/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingSeamCrossingCoordinates
import LeanTrominoes.GridSegmentRationalSeamPerturbation

/-! # A single rational row-seam shift realizes all finite-table port choices -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def seamPerturbationValues {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List (ℚ × ℚ) :=
  (seamCrossingCopies graph drawing 0).map fun key =>
    ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0,
      (drawing.liftedStraightSegment key.1 key.2).horizontalSeamVelocity)

def seamPerturbation {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : ℚ :=
  RationalPerturbation.slabPerturbation (seamPerturbationValues graph drawing)

def shiftedSeamAbscissa {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (key : Nat × Cell) : ℚ :=
  (drawing.liftedStraightSegment key.1 key.2).rationalAbscissaAt (-seamPerturbation graph drawing)

theorem seamPerturbation_positive {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) :
    0 < seamPerturbation graph drawing := RationalPerturbation.slabPerturbation_positive _

theorem mem_seamPerturbationValues {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) :
    ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0,
      (drawing.liftedStraightSegment key.1 key.2).horizontalSeamVelocity) ∈ seamPerturbationValues graph drawing :=
  List.mem_map.mpr ⟨key,member,rfl⟩

theorem shiftedSeamAbscissa_eq_evaluate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (key : Nat × Cell) :
    shiftedSeamAbscissa graph drawing key = RationalPerturbation.evaluate (seamPerturbation graph drawing)
      ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0,
        (drawing.liftedStraightSegment key.1 key.2).horizontalSeamVelocity) := by
  unfold shiftedSeamAbscissa RationalPerturbation.evaluate
  have atZero : (drawing.liftedStraightSegment key.1 key.2).rationalAbscissaAt (0 : ℚ) =
      (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0 := by
    simpa only [Int.cast_zero] using GridSegment.rationalAbscissaAt_int (drawing.liftedStraightSegment key.1 key.2) 0
  simpa only [Int.cast_zero,zero_sub,atZero] using
    GridSegment.rationalAbscissaAt_sub (drawing.liftedStraightSegment key.1 key.2) (0 : Int) (seamPerturbation graph drawing)

theorem shiftedSeamAbscissa_slab {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) :
    rationalSlab (shiftedSeamAbscissa graph drawing key) false =
      rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
        (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)) := by
  rw [seamTowardLeft_at_key planar straight 0 member]
  have result := GridSegment.shifted_horizontal_seam_slab (segment := drawing.liftedStraightSegment key.1 key.2) (line := 0)
    (seamPerturbation_positive graph drawing) (RationalPerturbation.slabPerturbation_lt_slabMargin (mem_seamPerturbationValues member))
  simpa only [Int.cast_zero,zero_sub,shiftedSeamAbscissa] using result

theorem shiftedSeamAbscissae_preserve_order {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {first second : Nat × Cell} (firstMember : first ∈ seamCrossingCopies graph drawing 0)
    (secondMember : second ∈ seamCrossingCopies graph drawing 0)
    (ordered : (drawing.liftedStraightSegment first.1 first.2).rationalLineAbscissa 0 <
      (drawing.liftedStraightSegment second.1 second.2).rationalLineAbscissa 0) :
    shiftedSeamAbscissa graph drawing first < shiftedSeamAbscissa graph drawing second := by
  rw [shiftedSeamAbscissa_eq_evaluate,shiftedSeamAbscissa_eq_evaluate]
  exact RationalPerturbation.slabPerturbation_preserves_order (mem_seamPerturbationValues firstMember)
    (mem_seamPerturbationValues secondMember) (Or.inl ordered)

end LeanTrominoes.PeriodicGridDrawing

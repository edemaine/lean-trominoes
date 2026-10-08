/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalEnlargedCrossingBars

/-! # Scaled lattice points in the narrow enlarged templates -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem enlargedRectangleTemplate_contains_scaled_grid_point {factor : Int} {radius : Nat}
    (spacing : 20*(radius : Int) < factor) {position anchor : Cell}
    (profile : AnchorProfile) (index : Fin 4)
    (contains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile index)
      (realCell (Cell.scale factor anchor))) : position = anchor := by
  have bounds := enlargedRectangleTemplate_real_bounds factor radius position profile index contains
  have nonnegative : (0 : Int) ≤ radius := by positivity
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor)
      (lower := -5*(radius : Int)) (upper := 5*radius)
      (point := (realCell (Cell.scale factor anchor)).1) (by omega) (by omega)
    · push_cast
      constructor <;> linarith [(abs_le.mp bounds.1).1,(abs_le.mp bounds.1).2]
    · simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast]
      constructor <;> linarith [show (0 : ℝ) ≤ radius by positivity]
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor)
      (lower := -10*(radius : Int)) (upper := 10*radius)
      (point := (realCell (Cell.scale factor anchor)).2) (by omega) (by omega)
    · push_cast
      constructor <;> linarith [(abs_le.mp bounds.2).1,(abs_le.mp bounds.2).2]
    · simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast]
      constructor <;> linarith [show (0 : ℝ) ≤ radius by positivity]

theorem enlargedCrossingBar_contains_scaled_grid_point {factor line ordinate : Int} {radius : Nat}
    (spacing : 10*(radius : Int) < factor) {anchor : Cell}
    (contains : GridPolyline.RealContains (enlargedCrossingBar factor radius line ordinate)
      (realCell (Cell.scale factor anchor))) : line = anchor.1 ∧ ordinate = factor*anchor.2 := by
  have bounds := enlargedCrossingBar_real_bounds factor radius line ordinate contains
  have nonnegative : (0 : Int) ≤ radius := by positivity
  refine ⟨?_,?_⟩
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor)
      (lower := -5*(radius : Int)) (upper := 5*radius)
      (point := (realCell (Cell.scale factor anchor)).1) (by omega) (by omega)
    · push_cast
      constructor <;> linarith [(abs_le.mp bounds.1).1,(abs_le.mp bounds.1).2]
    · simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast]
      constructor <;> linarith [show (0 : ℝ) ≤ radius by positivity]
  · have ordinateEq := bounds.2.symm
    simp only [realCell,Cell.scale,Int.cast_mul] at ordinateEq
    exact_mod_cast ordinateEq

end LeanTrominoes.OrthogonalDrawingRefinement

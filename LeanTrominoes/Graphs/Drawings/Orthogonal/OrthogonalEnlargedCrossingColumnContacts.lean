/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalEnlargedCrossingBars

/-! # A wide crossing bar meets only its own scaled integer column -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem enlargedCrossingBar_contact_scaled_column {factor line ordinate column : Int} {radius : Nat}
    (spacing : 10*(radius : Int) < factor) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (enlargedCrossingBar factor radius line ordinate) point)
    (atColumn : point.1 = (factor : ℝ)*column) : line = column := by
  have bounds := enlargedCrossingBar_real_bounds factor radius line ordinate contains
  have nonnegative : (0 : Int) ≤ radius := by positivity
  apply GridSegment.closed_interval_periodic_shifts_unique (period := factor)
    (lower := -5*(radius : Int)) (upper := 5*radius) (point := point.1) (by omega) (by omega)
  · push_cast
    constructor <;> linarith [(abs_le.mp bounds.1).1,(abs_le.mp bounds.1).2]
  · rw [atColumn]
    push_cast
    constructor <;> linarith [show (0 : ℝ) ≤ radius by positivity]

end LeanTrominoes.OrthogonalDrawingRefinement

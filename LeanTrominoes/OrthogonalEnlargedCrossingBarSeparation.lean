/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalEnlargedCrossingBars

/-! # Distinct wide bars in isolated column strips are disjoint -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem enlargedCrossingBars_contact_same_column {factor firstLine lastLine firstHeight lastHeight : Int} {radius : Nat}
    (spacing : 10*(radius : Int) < factor) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (enlargedCrossingBar factor radius firstLine firstHeight) point)
    (lastContains : GridPolyline.RealContains (enlargedCrossingBar factor radius lastLine lastHeight) point) :
    firstLine = lastLine ∧ firstHeight = lastHeight := by
  have firstBounds := enlargedCrossingBar_real_bounds _ _ _ _ firstContains
  have lastBounds := enlargedCrossingBar_real_bounds _ _ _ _ lastContains
  have nonnegative : (0 : Int) ≤ radius := by positivity
  refine ⟨?_,?_⟩
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -5*(radius : Int)) (upper := 5*radius)
      (point := point.1) (by omega) (by omega)
    all_goals
      push_cast
      constructor <;> linarith [(abs_le.mp firstBounds.1).1,(abs_le.mp firstBounds.1).2,
        (abs_le.mp lastBounds.1).1,(abs_le.mp lastBounds.1).2]
  · exact_mod_cast firstBounds.2.symm.trans lastBounds.2

end LeanTrominoes.OrthogonalDrawingRefinement

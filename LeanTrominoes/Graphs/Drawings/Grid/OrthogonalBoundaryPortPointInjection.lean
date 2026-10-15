/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryPortPointFaces

/-! # A proper integral boundary port is determined by its point -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

theorem Port.eq_of_point_eq {width height margin : Int}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (marginNonnegative : 0 ≤ margin) {first last : Port}
    (firstInside : first.Inside width height margin) (lastInside : last.Inside width height margin)
    (equal : first.point width height = last.point width height) : first = last := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨lastSide,lastCoordinate⟩ := last
  fin_cases firstSide <;> fin_cases lastSide
  all_goals simp_all [Port.point,Port.Inside]
  all_goals omega

end LeanTrominoes.OrthogonalBoundaryRouting

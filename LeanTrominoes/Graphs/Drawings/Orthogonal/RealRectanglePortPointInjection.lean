/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RealRectangleBoundaryOrientation

/-! # Proper boundary ports are determined by their geometric points -/
namespace LeanTrominoes.RealRectangleBoundary

theorem Port.eq_of_point_eq {width height : ℝ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    {first last : Port} (firstInside : first.Inside width height) (lastInside : last.Inside width height)
    (equal : first.point width height = last.point width height) : first = last := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨lastSide,lastCoordinate⟩ := last
  fin_cases firstSide <;> fin_cases lastSide
  all_goals simp_all [Port.point,Port.Inside,Port.extent]

end LeanTrominoes.RealRectangleBoundary

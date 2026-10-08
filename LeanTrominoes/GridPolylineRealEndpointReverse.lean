/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealAlgebra

/-! # Reversing a polyline preserves its endpoint set -/
namespace LeanTrominoes.GridPolyline

theorem realIsEndpoint_reverse (route : List Cell) (point : ℝ × ℝ) :
    RealIsEndpoint route.reverse point ↔ RealIsEndpoint route point := by
  simp only [RealIsEndpoint,List.head?_reverse,List.getLast?_reverse]
  exact or_comm

end LeanTrominoes.GridPolyline

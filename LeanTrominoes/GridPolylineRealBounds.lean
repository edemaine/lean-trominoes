/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealIntersection
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicGridDrawingRealGeometry

/-! # Real bounds from the integer points of a polygonal route -/
namespace LeanTrominoes.GridPolyline

theorem realContains_bounds {route : List Cell} {left right bottom top : Int}
    (bounds : ∀ vertex ∈ route, left ≤ vertex.1 ∧ vertex.1 ≤ right ∧ bottom ≤ vertex.2 ∧ vertex.2 ≤ top)
    {point : ℝ × ℝ} (contains : RealContains route point) :
    (left : ℝ) ≤ point.1 ∧ point.1 ≤ (right : ℝ) ∧ (bottom : ℝ) ≤ point.2 ∧ point.2 ≤ (top : ℝ) := by
  obtain ⟨segment,member,contains⟩ := contains
  have ends := gridPolylineSegments_endpoints_mem member
  have startBounds := bounds _ ends.1
  have finishBounds := bounds _ ends.2
  have box := GridSegment.realBoxContains_of_realContains contains
  exact ⟨le_trans (by exact_mod_cast le_min startBounds.1 finishBounds.1) box.1,
    le_trans box.2.1 (by exact_mod_cast max_le startBounds.2.1 finishBounds.2.1),
    le_trans (by exact_mod_cast le_min startBounds.2.2.1 finishBounds.2.2.1) box.2.2.1,
    le_trans box.2.2.2 (by exact_mod_cast max_le startBounds.2.2.2 finishBounds.2.2.2)⟩

end LeanTrominoes.GridPolyline

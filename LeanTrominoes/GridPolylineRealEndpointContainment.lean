/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealAlgebra
import LeanTrominoes.GridPolylineSegmentIndices

/-! # Every endpoint of a nontrivial route belongs to its real image -/
namespace LeanTrominoes.GridPolyline

theorem realContains_head {route : List Cell} (long : 2 ≤ route.length) {endpoint : Cell}
    (head : route.head? = some endpoint) : RealContains route (realCell endpoint) := by
  cases route with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      have equal : first = endpoint := by simpa using head
      subst first
      exact ⟨⟨endpoint,second⟩,by simp [gridPolylineSegments],GridSegment.realContains_start _⟩

theorem realContains_last {route : List Cell} (long : 2 ≤ route.length) {endpoint : Cell}
    (last : route.getLast? = some endpoint) : RealContains route (realCell endpoint) := by
  apply (realContains_reverse _ _).mp
  exact realContains_head (by simpa using long) (by simpa only [List.head?_reverse] using last)

theorem realContains_endpoint {route : List Cell} (long : 2 ≤ route.length) {point : ℝ × ℝ}
    (endpoint : RealIsEndpoint route point) : RealContains route point := by
  rcases endpoint with ⟨cell,head,rfl⟩ | ⟨cell,last,rfl⟩
  · exact realContains_head long head
  · exact realContains_last long last

end LeanTrominoes.GridPolyline

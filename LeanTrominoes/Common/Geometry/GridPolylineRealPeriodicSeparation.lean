/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealBounds
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.Geometry.GridSegmentRealPeriodicSeparation

/-! # Normalized real route images identify their periodic copy -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem realContains_translate_inverse (offset : Cell) (route : List Cell) (point : ℝ × ℝ) :
    RealContains (translatePolyline offset route) point ↔
      RealContains route (point.1-offset.1,point.2-offset.2) := by
  have translated := realContains_translate offset route (point.1-offset.1,point.2-offset.2)
  have x : (offset.1 : ℝ)+(point.1-offset.1) = point.1 := by ring
  have y : (offset.2 : ℝ)+(point.2-offset.2) = point.2 := by ring
  simpa only [x,y,Prod.mk.eta] using translated

theorem real_normalized_routes_cells_unique {first second : List Cell} {period : Int}
    (positive : 3 < period)
    (firstBounds : ∀ point ∈ first, 1 ≤ point.1 ∧ point.1 ≤ period-1 ∧ 1 ≤ point.2 ∧ point.2 ≤ 3)
    (secondBounds : ∀ point ∈ second, 1 ≤ point.1 ∧ point.1 ≤ period-1 ∧ 1 ≤ point.2 ∧ point.2 ≤ 3)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : RealContains (translatePolyline (Cell.scale period firstCell) first) point)
    (secondContains : RealContains (translatePolyline (Cell.scale period secondCell) second) point) :
    firstCell = secondCell := by
  have firstImage := (realContains_translate_inverse _ _ _).mp firstContains
  have secondImage := (realContains_translate_inverse _ _ _).mp secondContains
  have firstBox := realContains_bounds firstBounds firstImage
  have secondBox := realContains_bounds secondBounds secondImage
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul] at firstBox secondBox
  apply Prod.ext
  · apply GridSegment.normalized_bands_periodic_shifts_unique (point := point.1) (by omega : 0 < period)
      (by omega : (0 : Int) ≤ 1 ∧ period-1 < period) (by omega : (0 : Int) ≤ 1 ∧ period-1 < period)
    · exact ⟨by linarith [firstBox.1],by linarith [firstBox.2.1]⟩
    · exact ⟨by linarith [secondBox.1],by linarith [secondBox.2.1]⟩
  · apply GridSegment.normalized_bands_periodic_shifts_unique (point := point.2) (by omega : 0 < period)
      (by omega : (0 : Int) ≤ 1 ∧ (3 : Int) < period) (by omega : (0 : Int) ≤ 1 ∧ (3 : Int) < period)
    · exact ⟨by linarith [firstBox.2.2.1],by linarith [firstBox.2.2.2]⟩
    · exact ⟨by linarith [secondBox.2.2.1],by linarith [secondBox.2.2.2]⟩

end LeanTrominoes.GridPolyline

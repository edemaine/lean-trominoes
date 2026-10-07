/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRealGeometry
import LeanTrominoes.GridSegmentRealIntersection
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-! # Real locality from endpoint bounds in two adjacent fundamental cells -/
namespace LeanTrominoes.PeriodicGridDrawing

def PointInLocalRectangle (drawing : PeriodicGridDrawing) (offset point : Cell) : Prop :=
  min 0 ((drawing.gridSize : Int)*offset.1) ≤ point.1 ∧
    point.1 ≤ (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) ∧
    min 0 ((drawing.gridSize : Int)*offset.2) ≤ point.2 ∧
    point.2 ≤ (drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2)

theorem realContains_in_local_rectangle {drawing : PeriodicGridDrawing} {offset : Cell}
    {route : List Cell} (bounds : ∀ point ∈ route, drawing.PointInLocalRectangle offset point)
    {point : ℝ × ℝ} (member : GridPolyline.RealContains route point) :
    (min 0 ((drawing.gridSize : Int)*offset.1) : Int) ≤ point.1 ∧
      point.1 ≤ ((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) : Int) ∧
      (min 0 ((drawing.gridSize : Int)*offset.2) : Int) ≤ point.2 ∧
      point.2 ≤ ((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2) : Int) := by
  obtain ⟨segment,segmentMember,contains⟩ := member
  have endpoints := gridPolylineSegments_endpoints_mem segmentMember
  have start := bounds segment.start endpoints.1
  have finish := bounds segment.finish endpoints.2
  have box := GridSegment.realBoxContains_of_realContains contains
  refine ⟨le_trans ?_ box.1,le_trans box.2.1 ?_,le_trans ?_ box.2.2.1,le_trans box.2.2.2 ?_⟩
  · exact_mod_cast (le_min start.1 finish.1)
  · exact_mod_cast (max_le start.2.1 finish.2.1)
  · exact_mod_cast (le_min start.2.2.1 finish.2.2.1)
  · exact_mod_cast (max_le start.2.2.2 finish.2.2.2)

theorem real_local_of_rectangle {drawing : PeriodicGridDrawing} {offset : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs ≤ 1) {point : ℝ × ℝ}
    (bounds :
      (min 0 ((drawing.gridSize : Int)*offset.1) : Int) ≤ point.1 ∧
      point.1 ≤ ((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) : Int) ∧
      (min 0 ((drawing.gridSize : Int)*offset.2) : Int) ≤ point.2 ∧
      point.2 ≤ ((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2) : Int)) :
    drawing.RealPointInCell (0,0) point ∨ drawing.RealPointInCell offset point := by
  have offsets := PeriodicOrthocrossing.offset_eq_of_span_le_one (⟨(),(),offset⟩ : PeriodicEdge Unit) localOffset
  have positive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast (show 0 < drawing.gridSize from by unfold gridSize; omega)
  rcases offsets with rfl | rfl | rfl | rfl | rfl
  · left
    simpa [RealPointInCell] using bounds
  · by_cases side : point.1 ≤ drawing.gridSize
    · left
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨bounds.1,side,bounds.2.2⟩
    · right
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨by linarith,by linarith [bounds.2.1],bounds.2.2⟩
  · by_cases side : 0 ≤ point.1
    · left
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨side,bounds.2.1,bounds.2.2⟩
    · right
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨by simpa using bounds.1,by linarith,bounds.2.2⟩
  · by_cases side : point.2 ≤ drawing.gridSize
    · left
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨bounds.1,bounds.2.1,bounds.2.2.1,side⟩
    · right
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨bounds.1,bounds.2.1,by linarith,by linarith [bounds.2.2.2]⟩
  · by_cases side : 0 ≤ point.2
    · left
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨bounds.1,bounds.2.1,side,bounds.2.2.2⟩
    · right
      simp [positive.le,RealPointInCell] at bounds ⊢
      exact ⟨bounds.1,bounds.2.1,by simpa using bounds.2.2.1,by linarith⟩

end LeanTrominoes.PeriodicGridDrawing

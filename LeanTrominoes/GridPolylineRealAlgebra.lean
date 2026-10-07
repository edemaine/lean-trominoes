/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRealGeometry
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-! # Closed geometric images under route translation, reversal, and joining -/
namespace LeanTrominoes
open PeriodicOrthocrossing

namespace GridSegment

theorem realContains_reverse (segment : GridSegment) (point : ℝ × ℝ) :
    segment.reverse.RealContains point ↔ segment.RealContains point := by
  constructor
  all_goals
    rintro ⟨t,lo,hi,hx,hy⟩
    refine ⟨1-t,by linarith,by linarith,?_,?_⟩
    all_goals dsimp only [reverse] at hx hy ⊢; nlinarith

end GridSegment

namespace GridPolyline

theorem realContains_translate (offset : Cell) (route : List Cell) (point : ℝ × ℝ) :
    RealContains (translatePolyline offset route) (offset.1+point.1,offset.2+point.2) ↔
      RealContains route point := by
  unfold RealContains
  rw [gridPolylineSegments_translatePolyline]
  constructor
  · rintro ⟨segment,member,contains⟩
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact ⟨original,originalMember,(GridSegment.realContains_translate _ _ _).mp contains⟩
  · rintro ⟨segment,member,contains⟩
    exact ⟨segment.translate offset,List.mem_map.mpr ⟨segment,member,rfl⟩,
      (GridSegment.realContains_translate _ _ _).mpr contains⟩

theorem realContains_reverse (route : List Cell) (point : ℝ × ℝ) :
    RealContains route.reverse point ↔ RealContains route point := by
  unfold RealContains
  rw [gridPolylineSegments_reverse]
  constructor
  · rintro ⟨segment,member,contains⟩
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact ⟨original,List.mem_reverse.mp originalMember,(GridSegment.realContains_reverse _ _).mp contains⟩
  · rintro ⟨segment,member,contains⟩
    exact ⟨segment.reverse,List.mem_map.mpr ⟨segment,List.mem_reverse.mpr member,rfl⟩,
      (GridSegment.realContains_reverse _ _).mpr contains⟩

theorem realContains_join {first second : List Cell} {boundary : Cell}
    (firstLast : first.getLast? = some boundary) (secondHead : second.head? = some boundary)
    (point : ℝ × ℝ) :
    RealContains (joinPolylines first second) point ↔ RealContains first point ∨ RealContains second point := by
  unfold RealContains
  rw [gridPolylineSegments_joinPolylines firstLast secondHead]
  simp only [List.mem_append,or_and_right,exists_or]

end GridPolyline
end LeanTrominoes

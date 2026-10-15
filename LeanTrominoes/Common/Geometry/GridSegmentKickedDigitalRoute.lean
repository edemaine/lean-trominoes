/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentDigitalRoute

/-! # Digital cores with horizontal endpoint steps

A one-unit horizontal step at each end keeps the rasterized middle strictly
between the two port columns. The complete route stays within coordinate
distance three of its straight core. Both horizontal orientations use the
same construction, with `side = 1` or `side = -1`.
-/
namespace LeanTrominoes.GridSegment
open PeriodicOrthocrossing

def kickedSegment (segment : GridSegment) (side : Int) : GridSegment :=
  ⟨(segment.start.1+side,segment.start.2),
    (segment.finish.1-side,segment.finish.2)⟩

noncomputable def kickedDigitalWalk (segment : GridSegment) (side : Int) : List Cell :=
  joinAtEndpoint
    (joinAtEndpoint [segment.start,(segment.kickedSegment side).start]
      (segment.kickedSegment side).digitalRoute)
    [(segment.kickedSegment side).finish,segment.finish]

@[simp] theorem kickedDigitalWalk_head (segment : GridSegment) (side : Int) :
    (segment.kickedDigitalWalk side).head? = some segment.start := by
  exact joinAtEndpoint_head? (joinAtEndpoint_head? (by simp))

@[simp] theorem kickedDigitalWalk_last (segment : GridSegment) (side : Int) :
    (segment.kickedDigitalWalk side).getLast? = some segment.finish := by
  exact joinAtEndpoint_getLast?
    (joinAtEndpoint_getLast? (by simp) (digitalRoute_head _) (digitalRoute_last _))
    (by simp) (by simp)

theorem kickedDigitalWalk_nonempty (segment : GridSegment) (side : Int) :
    segment.kickedDigitalWalk side ≠ [] := by
  intro empty
  have head := segment.kickedDigitalWalk_head side
  simp [empty] at head

theorem kickedDigitalWalk_orthogonal (segment : GridSegment) {side : Int} (nonzero : side ≠ 0) :
    PeriodicOrthocrossing.OrthogonalPolyline (segment.kickedDigitalWalk side) := by
  have first : PeriodicOrthocrossing.OrthogonalPolyline
      [segment.start,(segment.kickedSegment side).start] := by
    simp [PeriodicOrthocrossing.OrthogonalPolyline,kickedSegment,
      IsAxisAligned,IsHorizontal,nonzero]
  have last : PeriodicOrthocrossing.OrthogonalPolyline
      [(segment.kickedSegment side).finish,segment.finish] := by
    simp [PeriodicOrthocrossing.OrthogonalPolyline,kickedSegment,
      IsAxisAligned,IsHorizontal,nonzero]
  exact (first.joinAtEndpoint (digitalRoute_orthogonal _) (by simp) (digitalRoute_head _)).joinAtEndpoint
    last (joinAtEndpoint_getLast? (by simp) (digitalRoute_head _) (digitalRoute_last _)) (by simp)

theorem kickedDigitalWalk_contains (segment : GridSegment) (side : Int) (point : ℝ × ℝ) :
    GridPolyline.RealContains (segment.kickedDigitalWalk side) point ↔
      (⟨segment.start,(segment.kickedSegment side).start⟩ : GridSegment).RealContains point ∨
      GridPolyline.RealContains (segment.kickedSegment side).digitalRoute point ∨
      (⟨(segment.kickedSegment side).finish,segment.finish⟩ : GridSegment).RealContains point := by
  have firstLast : (joinPolylines [segment.start,(segment.kickedSegment side).start]
      (segment.kickedSegment side).digitalRoute).getLast? = some (segment.kickedSegment side).finish :=
    joinAtEndpoint_getLast? (by simp) (digitalRoute_head _) (digitalRoute_last _)
  change GridPolyline.RealContains
    (joinPolylines (joinPolylines [segment.start,(segment.kickedSegment side).start]
      (segment.kickedSegment side).digitalRoute)
      [(segment.kickedSegment side).finish,segment.finish]) point ↔ _
  rw [GridPolyline.realContains_join firstLast (by simp),
    GridPolyline.realContains_join (by simp) (digitalRoute_head _)]
  simp only [GridPolyline.RealContains,gridPolylineSegments,List.mem_singleton,exists_eq_left,or_assoc]

theorem kickedSegment_tube (segment : GridSegment) {side : Int} (small : |side| ≤ 1)
    {point : ℝ × ℝ} (contains : (segment.kickedSegment side).RealContains point) :
    segment.RealTubeContains 1 point := by
  have realSmall : |(side : ℝ)| ≤ 1 := by exact_mod_cast small
  have start : segment.RealTubeContains 1 (realCell (segment.kickedSegment side).start) := by
    refine ⟨realCell segment.start,realContains_start _,?_,?_⟩
    · simpa [realCell,kickedSegment] using realSmall
    · simp [realCell,kickedSegment]
  have finish : segment.RealTubeContains 1 (realCell (segment.kickedSegment side).finish) := by
    refine ⟨realCell segment.finish,realContains_finish _,?_,?_⟩
    · simpa [realCell,kickedSegment] using realSmall
    · simp [realCell,kickedSegment]
  exact start.segment finish contains

theorem kickedDigitalWalk_tube (segment : GridSegment) {side : Int} (small : |side| ≤ 1)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalWalk side) point) :
    segment.RealTubeContains 3 point := by
  rcases (segment.kickedDigitalWalk_contains side point).mp contains with first | middle | last
  · have finish := segment.kickedSegment_tube small (realContains_start _)
    have start : segment.RealTubeContains 1 (realCell segment.start) :=
      ⟨realCell segment.start,realContains_start _,by simp,by simp⟩
    exact (RealTubeContains.segment (output := ⟨segment.start,(segment.kickedSegment side).start⟩)
      start finish first).mono (by norm_num)
  · simpa only [show (1 : ℝ)+2 = 3 by norm_num] using
      ((segment.kickedSegment side).digitalRoute_tube middle).compose
        (fun _ contains => segment.kickedSegment_tube small contains)
  · have start := segment.kickedSegment_tube small (realContains_finish _)
    have finish : segment.RealTubeContains 1 (realCell segment.finish) :=
      ⟨realCell segment.finish,realContains_finish _,by simp,by simp⟩
    exact (RealTubeContains.segment (output := ⟨(segment.kickedSegment side).finish,segment.finish⟩)
      start finish last).mono (by norm_num)

noncomputable def kickedDigitalRoute (segment : GridSegment) (side : Int) : List Cell :=
  AxisDirection.normalizeOrthogonalPolyline (segment.kickedDigitalWalk side)

@[simp] theorem kickedDigitalRoute_head (segment : GridSegment) {side : Int} (nonzero : side ≠ 0) :
    (segment.kickedDigitalRoute side).head? = some segment.start :=
  (AxisDirection.normalizeOrthogonalPolyline_head? (segment.kickedDigitalWalk_nonempty side)
    (segment.kickedDigitalWalk_orthogonal nonzero)).trans (segment.kickedDigitalWalk_head side)

@[simp] theorem kickedDigitalRoute_last (segment : GridSegment) {side : Int} (nonzero : side ≠ 0) :
    (segment.kickedDigitalRoute side).getLast? = some segment.finish :=
  (AxisDirection.normalizeOrthogonalPolyline_getLast? (segment.kickedDigitalWalk_nonempty side)
    (segment.kickedDigitalWalk_orthogonal nonzero)).trans (segment.kickedDigitalWalk_last side)

theorem kickedDigitalRoute_orthogonal (segment : GridSegment) {side : Int} (nonzero : side ≠ 0) :
    PeriodicOrthocrossing.OrthogonalPolyline (segment.kickedDigitalRoute side) :=
  AxisDirection.normalizeOrthogonalPolyline_orthogonal (segment.kickedDigitalWalk_nonempty side)
    (segment.kickedDigitalWalk_orthogonal nonzero)

theorem kickedDigitalRoute_simple {segment : GridSegment} {side : Int} (nonzero : side ≠ 0)
    (different : segment.start ≠ segment.finish) :
    GridPolyline.IsRealOpenSimple (segment.kickedDigitalRoute side) :=
  AxisDirection.normalizeOrthogonalPolyline_realOpenSimple (segment.kickedDigitalWalk_nonempty side)
    (segment.kickedDigitalWalk_orthogonal nonzero) (segment.kickedDigitalWalk_head side)
    (segment.kickedDigitalWalk_last side) different

theorem kickedDigitalRoute_contains {segment : GridSegment} {side : Int} (nonzero : side ≠ 0)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point) :
    GridPolyline.RealContains (segment.kickedDigitalWalk side) point :=
  AxisDirection.normalizeOrthogonalPolyline_realContains (segment.kickedDigitalWalk_nonempty side)
    (segment.kickedDigitalWalk_orthogonal nonzero) contains

theorem kickedDigitalRoute_tube (segment : GridSegment) {side : Int} (nonzero : side ≠ 0)
    (small : |side| ≤ 1) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point) :
    segment.RealTubeContains 3 point :=
  segment.kickedDigitalWalk_tube small (kickedDigitalRoute_contains nonzero contains)

end LeanTrominoes.GridSegment

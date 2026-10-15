/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentDigitalSamples
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineRealLoopErasure
import LeanTrominoes.Common.Geometry.GridPolylineRealBounds

/-! # Simple orthogonal digital routes for arbitrary grid segments

Every straight segment has an orthogonal route with the same endpoints and
coordinate error at most two. Distinct endpoints give an open simple route.
The tube-separation theorem then excludes crossings between digital routes
of disjoint input segments after a linear refinement.
-/
namespace LeanTrominoes.GridSegment

noncomputable def digitalWalk (segment : GridSegment) : List Cell :=
  GridPolyline.rectilinearize (segment.digitalSamples 0 segment.digitalSteps)

@[simp] theorem digitalWalk_head (segment : GridSegment) :
    segment.digitalWalk.head? = some segment.start := by
  simp [digitalWalk]

@[simp] theorem digitalWalk_last (segment : GridSegment) :
    segment.digitalWalk.getLast? = some segment.finish := by
  simp [digitalWalk]

theorem digitalWalk_nonempty (segment : GridSegment) : segment.digitalWalk ≠ [] := by
  intro empty
  have head := segment.digitalWalk_head
  simp [empty] at head

theorem digitalWalk_orthogonal (segment : GridSegment) :
    PeriodicOrthocrossing.OrthogonalPolyline segment.digitalWalk :=
  GridPolyline.rectilinearize_orthogonal _

theorem digitalWalk_tube (segment : GridSegment) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains segment.digitalWalk point) : segment.RealTubeContains 2 point := by
  apply GridPolyline.rectilinearize_realContains_tube (points := segment.digitalSamples 0 segment.digitalSteps)
      (contains := contains)
  · intro sample member
    obtain ⟨index,_,valid,equal⟩ := digitalSamples_member member
    rw [equal]
    obtain ⟨original,originalContains,nearX,nearY⟩ := segment.digitalSample_tube (by simpa using valid)
    exact ⟨original,originalContains,nearX.trans (by norm_num),nearY.trans (by norm_num)⟩
  · intro piece member
    obtain ⟨index,_,valid,equal⟩ := digitalSamples_segment member
    rw [equal]
    exact segment.digitalSample_corner_tube (by simpa using valid)

theorem digitalWalk_points_box (segment : GridSegment) :
    ∀ point ∈ segment.digitalWalk,
      min segment.start.1 segment.finish.1 ≤ point.1 ∧ point.1 ≤ max segment.start.1 segment.finish.1 ∧
      min segment.start.2 segment.finish.2 ≤ point.2 ∧ point.2 ≤ max segment.start.2 segment.finish.2 := by
  apply GridPolyline.rectilinearize_points_property
  · intro sample member
    obtain ⟨index,_,valid,equal⟩ := digitalSamples_member member
    rw [equal]
    exact segment.digitalSample_box (by simpa using valid)
  · intro piece member
    obtain ⟨index,_,valid,equal⟩ := digitalSamples_segment member
    rw [equal]
    have firstBox := segment.digitalSample_box (index := index) (by omega)
    have nextBox := segment.digitalSample_box (index := index+1) (by omega)
    exact ⟨nextBox.1,nextBox.2.1,firstBox.2.2.1,firstBox.2.2.2⟩

/-- Verified loop erasure removes any incidental revisits in the sampled
walk while retaining the complete geometric tube bound. -/
noncomputable def digitalRoute (segment : GridSegment) : List Cell :=
  AxisDirection.normalizeOrthogonalPolyline segment.digitalWalk

@[simp] theorem digitalRoute_head (segment : GridSegment) :
    segment.digitalRoute.head? = some segment.start :=
  (AxisDirection.normalizeOrthogonalPolyline_head? segment.digitalWalk_nonempty segment.digitalWalk_orthogonal).trans
    segment.digitalWalk_head

@[simp] theorem digitalRoute_last (segment : GridSegment) :
    segment.digitalRoute.getLast? = some segment.finish :=
  (AxisDirection.normalizeOrthogonalPolyline_getLast? segment.digitalWalk_nonempty segment.digitalWalk_orthogonal).trans
    segment.digitalWalk_last

theorem digitalRoute_orthogonal (segment : GridSegment) :
    PeriodicOrthocrossing.OrthogonalPolyline segment.digitalRoute :=
  AxisDirection.normalizeOrthogonalPolyline_orthogonal segment.digitalWalk_nonempty segment.digitalWalk_orthogonal

theorem digitalRoute_simple {segment : GridSegment} (different : segment.start ≠ segment.finish) :
    GridPolyline.IsRealOpenSimple segment.digitalRoute :=
  AxisDirection.normalizeOrthogonalPolyline_realOpenSimple segment.digitalWalk_nonempty segment.digitalWalk_orthogonal
    segment.digitalWalk_head segment.digitalWalk_last different

theorem digitalRoute_tube (segment : GridSegment) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains segment.digitalRoute point) : segment.RealTubeContains 2 point :=
  AxisDirection.normalizeOrthogonalPolyline_tube segment.digitalWalk_nonempty segment.digitalWalk_orthogonal
    (fun _ contains => segment.digitalWalk_tube contains) contains

theorem digitalRoute_box (segment : GridSegment) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains segment.digitalRoute point) : segment.RealBoxContains point :=
  GridPolyline.realContains_bounds segment.digitalWalk_points_box
    (AxisDirection.normalizeOrthogonalPolyline_realContains segment.digitalWalk_nonempty segment.digitalWalk_orthogonal contains)

theorem digitalRoutes_disjoint {bound factor : Int} (boundPositive : 1 ≤ bound)
    (spacing : 8*bound < factor) {first second : GridSegment}
    (firstBounds : |first.direction.1| ≤ bound ∧ |first.direction.2| ≤ bound)
    (secondBounds : |second.direction.1| ≤ bound ∧ |second.direction.2| ≤ bound)
    (disjoint : ∀ point : ℝ × ℝ, first.RealContains point → ¬second.RealContains point)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (first.scale factor).digitalRoute point) :
    ¬GridPolyline.RealContains (second.scale factor).digitalRoute point := by
  intro secondContains
  have realSpacing : 4*(bound : ℝ)*2 < factor := by
    have castSpacing : (8 : ℝ)*bound < factor := by exact_mod_cast spacing
    nlinarith
  exact scaled_tubes_disjoint boundPositive (by norm_num) realSpacing firstBounds secondBounds disjoint point
    ((first.scale factor).digitalRoute_tube firstContains) ((second.scale factor).digitalRoute_tube secondContains)

end LeanTrominoes.GridSegment

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalSlabRealRouting
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisBox
import LeanTrominoes.Graphs.Drawings.Orthogonal.Orthogonal.PeriodicOrthocrossingOrthogonal

/-! # Simple orthogonal polylines for the ordered slab tracks -/
namespace LeanTrominoes.OrthogonalSlabRouting
open PeriodicOrthocrossing

def route (left right track source target : Int) : List Cell :=
  if source = target then [(left,source),(right,target)]
  else [(left,source),(track,source),(track,target),(right,target)]

theorem route_head (left right track source target : Int) :
    (route left right track source target).head? = some (left,source) := by
  by_cases equal : source = target <;> simp [route,equal]

theorem route_last (left right track source target : Int) :
    (route left right track source target).getLast? = some (right,target) := by
  by_cases equal : source = target <;> simp [route,equal]

theorem route_orthogonal {left right track source target : Int}
    (inside : left < track ∧ track < right) : OrthogonalPolyline (route left right track source target) := by
  by_cases equal : source = target
  all_goals simp [route,equal,OrthogonalPolyline,gridPolylineSegments,GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal,GridSegment.IsVertical]
  all_goals omega

theorem route_isRealOpenSimple {left right track source target : Int}
    (inside : left < track ∧ track < right) : GridPolyline.IsRealOpenSimple (route left right track source target) := by
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  by_cases equal : source = target
  all_goals simp [route,equal,GridPolyline.SimpleBoxCertificate,gridPolylineSegments,
    GridSegment.BoxIntersectionIsPoint]
  all_goals omega

theorem route_image {left right track source target : Int}
    (inside : left < track ∧ track < right) (point : ℝ × ℝ) :
    GridPolyline.RealContains (route left right track source target) point ↔
      ∃ segment ∈ segments left right track source target, segment.RealContains point := by
  by_cases equal : source = target
  · subst target
    simp only [route,ite_true,GridPolyline.RealContains,gridPolylineSegments,List.mem_cons,
      List.not_mem_nil,or_false,exists_eq_left,segments]
    constructor
    · intro contains
      have bounds := GridSegment.realBoxContains_of_realContains contains
      have rawXBounds : ((min left right : Int) : ℝ) ≤ point.1 ∧ point.1 ≤ ((max left right : Int) : ℝ) :=
        ⟨bounds.1,bounds.2.1⟩
      have xBounds : (left : ℝ) ≤ point.1 ∧ point.1 ≤ right := by
        simpa [min_eq_left (by omega : left ≤ right),max_eq_right (by omega : left ≤ right)] using rawXBounds
      have yEq : point.2 = (source : ℝ) := by simpa using le_antisymm bounds.2.2.2 bounds.2.2.1
      by_cases before : point.1 ≤ track
      · refine ⟨⟨(left,source),(track,source)⟩,Or.inl rfl,?_⟩
        apply GridSegment.realContains_of_axis_box (Or.inl ⟨rfl,by change left ≠ track; omega⟩)
        simpa [GridSegment.RealBoxContains,yEq,min_eq_left inside.1.le,max_eq_right inside.1.le] using
          ⟨xBounds.1,before⟩
      · refine ⟨⟨(track,source),(right,source)⟩,Or.inr (Or.inr rfl),?_⟩
        apply GridSegment.realContains_of_axis_box (Or.inl ⟨rfl,by change track ≠ right; omega⟩)
        simpa [GridSegment.RealBoxContains,yEq,min_eq_left inside.2.le,max_eq_right inside.2.le] using
          ⟨le_of_lt (lt_of_not_ge before),xBounds.2⟩
    · rintro ⟨segment,rfl | rfl | rfl,contains⟩
      all_goals
        have bounds := GridSegment.realBoxContains_of_realContains contains
        apply GridSegment.realContains_of_axis_box (Or.inl ⟨rfl,by change left ≠ right; omega⟩)
        simp only [GridSegment.RealBoxContains] at bounds ⊢
        norm_num only [min_self,max_self] at bounds ⊢
        have leftTrack : (left : ℝ) < track := by exact_mod_cast inside.1
        have trackRight : (track : ℝ) < right := by exact_mod_cast inside.2
        simp only [min_eq_left inside.1.le,max_eq_right inside.1.le,
          min_eq_left inside.2.le,max_eq_right inside.2.le,
          min_eq_left (by omega : left ≤ right),max_eq_right (by omega : left ≤ right)] at bounds ⊢
        exact ⟨by linarith [bounds.1],by linarith [bounds.2.1],bounds.2.2⟩
  · simp [route,equal,GridPolyline.RealContains,gridPolylineSegments,segments]

theorem routes_disjoint {left right gap count firstRank secondRank firstSource firstTarget secondSource secondTarget : Int}
    (gapPositive : 0 < gap) (firstRankPositive : 0 < firstRank) (rankOrder : firstRank < secondRank)
    (rankBound : secondRank ≤ count) (room : left+gap*count < right-gap*count)
    (sourceOrder : firstSource < secondSource) (targetOrder : firstTarget < secondTarget)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (route left right (bend left right gap firstRank firstSource firstTarget) firstSource firstTarget) point)
    (secondContains : GridPolyline.RealContains
      (route left right (bend left right gap secondRank secondSource secondTarget) secondSource secondTarget) point) : False := by
  obtain ⟨first,firstMember,firstContains⟩ := (route_image
    (bend_inside gapPositive firstRankPositive (by omega) room) point).mp firstContains
  obtain ⟨second,secondMember,secondContains⟩ := (route_image
    (bend_inside gapPositive (by omega) rankBound room) point).mp secondContains
  exact real_tracks_disjoint gapPositive firstRankPositive rankOrder rankBound room sourceOrder targetOrder
    first firstMember second secondMember point ⟨firstContains,secondContains⟩

end LeanTrominoes.OrthogonalSlabRouting

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalSlabRouteGeometry

/-! # Slab-route bounds and rigidity at the two vertical boundaries -/
namespace LeanTrominoes.OrthogonalSlabRouting

theorem route_real_bounds {left right track source target : Int}
    (inside : left < track ∧ track < right) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (route left right track source target) point) :
    (left : ℝ) ≤ point.1 ∧ point.1 ≤ right ∧
      (min source target : Int) ≤ point.2 ∧ point.2 ≤ (max source target : Int) := by
  obtain ⟨segment,member,contains⟩ := (route_image inside point).mp contains
  simp only [segments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    have bounds := GridSegment.realBoxContains_of_realContains contains
    simp only [GridSegment.RealBoxContains,Prod.fst,Prod.snd] at bounds
    simp only [min_eq_left inside.1.le,max_eq_right inside.1.le,
      min_eq_left inside.2.le,max_eq_right inside.2.le,min_self,max_self] at bounds
    push_cast at bounds ⊢
    have leftTrack : (left : ℝ) < track := by exact_mod_cast inside.1
    have trackRight : (track : ℝ) < right := by exact_mod_cast inside.2
    have minSource := min_le_left (source : ℝ) (target : ℝ)
    have minTarget := min_le_right (source : ℝ) (target : ℝ)
    have maxSource := le_max_left (source : ℝ) (target : ℝ)
    have maxTarget := le_max_right (source : ℝ) (target : ℝ)
    exact ⟨by linarith [bounds.1],by linarith [bounds.2.1],
      by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩

theorem route_left_boundary {left right track source target : Int}
    (inside : left < track ∧ track < right) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (route left right track source target) point)
    (onLeft : point.1 = (left : ℝ)) : point = realCell (left,source) := by
  obtain ⟨segment,member,contains⟩ := (route_image inside point).mp contains
  simp only [segments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    have bounds := GridSegment.realBoxContains_of_realContains contains
    simp only [GridSegment.RealBoxContains,Prod.fst,Prod.snd] at bounds
    simp only [min_eq_left inside.1.le,max_eq_right inside.1.le,
      min_eq_left inside.2.le,max_eq_right inside.2.le,min_self,max_self] at bounds
    have leftTrack : (left : ℝ) < track := by exact_mod_cast inside.1
    first
    | exact Prod.ext onLeft (by simpa only [realCell,Prod.snd] using le_antisymm bounds.2.2.2 bounds.2.2.1)
    | exfalso; linarith [bounds.1]

theorem route_right_boundary {left right track source target : Int}
    (inside : left < track ∧ track < right) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (route left right track source target) point)
    (onRight : point.1 = (right : ℝ)) : point = realCell (right,target) := by
  obtain ⟨segment,member,contains⟩ := (route_image inside point).mp contains
  simp only [segments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    have bounds := GridSegment.realBoxContains_of_realContains contains
    simp only [GridSegment.RealBoxContains,Prod.fst,Prod.snd] at bounds
    simp only [min_eq_left inside.1.le,max_eq_right inside.1.le,
      min_eq_left inside.2.le,max_eq_right inside.2.le,min_self,max_self] at bounds
    have trackRight : (track : ℝ) < right := by exact_mod_cast inside.2
    first
    | exact Prod.ext onRight (by simpa only [realCell,Prod.snd] using le_antisymm bounds.2.2.2 bounds.2.2.1)
    | exfalso; linarith [bounds.2.1]

theorem consecutive_routes_contact_joint {left middle right firstTrack secondTrack firstSource joint secondTarget : Int}
    (firstInside : left < firstTrack ∧ firstTrack < middle)
    (secondInside : middle < secondTrack ∧ secondTrack < right) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (route left middle firstTrack firstSource joint) point)
    (secondContains : GridPolyline.RealContains (route middle right secondTrack joint secondTarget) point) :
    point = realCell (middle,joint) := by
  have firstBounds := route_real_bounds firstInside firstContains
  have secondBounds := route_real_bounds secondInside secondContains
  exact route_right_boundary firstInside firstContains (le_antisymm firstBounds.2.1 secondBounds.1)

theorem separated_routes_disjoint {firstLeft firstRight secondLeft secondRight firstTrack secondTrack firstSource firstTarget secondSource secondTarget : Int}
    (firstInside : firstLeft < firstTrack ∧ firstTrack < firstRight)
    (secondInside : secondLeft < secondTrack ∧ secondTrack < secondRight) (separated : firstRight < secondLeft)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (route firstLeft firstRight firstTrack firstSource firstTarget) point)
    (secondContains : GridPolyline.RealContains (route secondLeft secondRight secondTrack secondSource secondTarget) point) : False := by
  have firstBounds := route_real_bounds firstInside firstContains
  have secondBounds := route_real_bounds secondInside secondContains
  have gap : (firstRight : ℝ) < secondLeft := by exact_mod_cast separated
  linarith [firstBounds.2.1,secondBounds.1]

end LeanTrominoes.OrthogonalSlabRouting

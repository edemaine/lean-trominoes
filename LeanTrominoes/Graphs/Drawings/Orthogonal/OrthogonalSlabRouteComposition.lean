/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalSlabRouteBounds
import LeanTrominoes.Common.Geometry.GridPolylineRealJoinOpenSimple

/-! # Composing simple orthogonal routes through consecutive slabs -/
namespace LeanTrominoes.OrthogonalSlabRouting
open PeriodicOrthocrossing

structure SlabRoute where
  left : Int
  right : Int
  source : Int
  target : Int
  points : List Cell
  deriving DecidableEq, Repr

def SlabRoute.start (slab : SlabRoute) : Cell := (slab.left,slab.source)
def SlabRoute.finish (slab : SlabRoute) : Cell := (slab.right,slab.target)

structure SlabRoute.IsValid (slab : SlabRoute) : Prop where
  ordered : slab.left < slab.right
  head : slab.points.head? = some slab.start
  last : slab.points.getLast? = some slab.finish
  simple : GridPolyline.IsRealOpenSimple slab.points
  orthogonal : OrthogonalPolyline slab.points
  bounds : ∀ point, GridPolyline.RealContains slab.points point →
    (slab.left : ℝ) ≤ point.1 ∧ point.1 ≤ slab.right
  leftBoundary : ∀ point, GridPolyline.RealContains slab.points point →
    point.1 = (slab.left : ℝ) → point = realCell slab.start
  rightBoundary : ∀ point, GridPolyline.RealContains slab.points point →
    point.1 = (slab.right : ℝ) → point = realCell slab.finish

def SlabRoute.ofTrack (left right track source target : Int) : SlabRoute :=
  ⟨left,right,source,target,route left right track source target⟩

theorem SlabRoute.ofTrack_valid {left right track source target : Int}
    (inside : left < track ∧ track < right) : (SlabRoute.ofTrack left right track source target).IsValid where
  ordered := by dsimp only [ofTrack]; omega
  head := route_head ..
  last := route_last ..
  simple := route_isRealOpenSimple inside
  orthogonal := route_orthogonal inside
  bounds := fun _ contains => ⟨(route_real_bounds inside contains).1,(route_real_bounds inside contains).2.1⟩
  leftBoundary := fun _ contains atLeft => route_left_boundary inside contains atLeft
  rightBoundary := fun _ contains atRight => route_right_boundary inside contains atRight

def SlabRoute.join (first second : SlabRoute) : SlabRoute :=
  ⟨first.left,second.right,first.source,second.target,joinPolylines first.points second.points⟩

theorem SlabRoute.join_valid {first second : SlabRoute} (firstValid : first.IsValid) (secondValid : second.IsValid)
    (sameX : first.right = second.left) (sameY : first.target = second.source) : (first.join second).IsValid := by
  have joint : first.finish = second.start := Prod.ext sameX sameY
  have secondHead : second.points.head? = some first.finish := secondValid.head.trans (congrArg some joint.symm)
  have contacts : ∀ point, GridPolyline.RealContains first.points point → GridPolyline.RealContains second.points point →
      point = realCell first.finish := by
    intro point firstContains secondContains
    have fb := firstValid.bounds point firstContains
    have sb := secondValid.bounds point secondContains
    rw [← sameX] at sb
    exact firstValid.rightBoundary point firstContains (le_antisymm fb.2 sb.1)
  have images (point : ℝ × ℝ) : GridPolyline.RealContains (first.join second).points point ↔
      GridPolyline.RealContains first.points point ∨ GridPolyline.RealContains second.points point :=
    GridPolyline.realContains_join firstValid.last secondHead point
  have firstOrdered : (first.left : ℝ) < first.right := by exact_mod_cast firstValid.ordered
  have secondOrdered : (second.left : ℝ) < second.right := by exact_mod_cast secondValid.ordered
  have sameRealX : (first.right : ℝ) = second.left := by exact_mod_cast sameX
  have firstLt := firstValid.ordered
  have secondLt := secondValid.ordered
  refine ⟨by dsimp only [join]; omega,?_,?_,?_,?_,?_,?_,?_⟩
  · have nonempty : first.points ≠ [] := by
      have long := firstValid.simple.1
      intro empty
      simp [empty] at long
    exact (joinPolylines_head?_of_first nonempty).trans firstValid.head
  · exact (joinPolylines_getLast?_of_second secondValid.simple.1).trans secondValid.last
  · exact GridPolyline.isRealOpenSimple_join firstValid.simple secondValid.simple firstValid.last secondHead contacts
  · exact isChain_joinPolylines firstValid.orthogonal secondValid.orthogonal (firstValid.last.trans secondHead.symm)
  · intro point contains
    rcases (images point).mp contains with contains | contains
    · have bounds := firstValid.bounds point contains
      exact ⟨bounds.1,by dsimp only [join]; linarith [bounds.2]⟩
    · have bounds := secondValid.bounds point contains
      exact ⟨by dsimp only [join]; linarith [bounds.1],bounds.2⟩
  · intro point contains atLeft
    rcases (images point).mp contains with contains | contains
    · exact firstValid.leftBoundary point contains atLeft
    · have bounds := secondValid.bounds point contains
      change point.1 = (first.left : ℝ) at atLeft
      exfalso
      linarith [bounds.1]
  · intro point contains atRight
    rcases (images point).mp contains with contains | contains
    · have bounds := firstValid.bounds point contains
      change point.1 = (second.right : ℝ) at atRight
      exfalso
      linarith [bounds.2]
    · exact secondValid.rightBoundary point contains atRight

end LeanTrominoes.OrthogonalSlabRouting

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcRouting
import LeanTrominoes.GridPolylineRealBounds

/-! # Inner arcs occupy distinct rectangular boundaries -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

def Port.normal (width height depth : Int) (port : Port) : GridSegment :=
  ⟨port.point width height,port.innerPoint width height depth⟩

def InnerBoundary (width height depth : Int) (point : ℝ × ℝ) : Prop :=
  (depth : ℝ) ≤ point.1 ∧ point.1 ≤ ((width-depth : Int) : ℝ) ∧
    (depth : ℝ) ≤ point.2 ∧ point.2 ≤ ((height-depth : Int) : ℝ) ∧
    (point.1 = (depth : ℝ) ∨ point.1 = ((width-depth : Int) : ℝ) ∨
      point.2 = (depth : ℝ) ∨ point.2 = ((height-depth : Int) : ℝ))

set_option maxHeartbeats 1000000

theorem innerArc_vertex_bounds {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) :
    ∀ vertex ∈ innerArc width height depth first second,
      depth ≤ vertex.1 ∧ vertex.1 ≤ width-depth ∧ depth ≤ vertex.2 ∧ vertex.2 ≤ height-depth := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Before,Port.Inside] at ordered firstInside secondInside <;>
    simp [innerArc,corner,Port.innerPoint] <;> omega

theorem innerArc_segments_boundary {width height depth : Int} {first second : Port}
    (ordered : first.Before second) :
    ∀ segment ∈ gridPolylineSegments (innerArc width height depth first second),
      (segment.start.1 = depth ∧ segment.finish.1 = depth) ∨
      (segment.start.1 = width-depth ∧ segment.finish.1 = width-depth) ∨
      (segment.start.2 = depth ∧ segment.finish.2 = depth) ∨
      (segment.start.2 = height-depth ∧ segment.finish.2 = height-depth) := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Before] at ordered <;>
    simp [innerArc,corner,Port.innerPoint,gridPolylineSegments] <;> omega

theorem innerArc_real_boundary {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (innerArc width height depth first second) point) :
    InnerBoundary width height depth point := by
  have bounds := GridPolyline.realContains_bounds
    (innerArc_vertex_bounds positive depthBound room firstInside secondInside ordered) contains
  obtain ⟨segment,member,t,lo,hi,hx,hy⟩ := contains
  refine ⟨bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2,?_⟩
  rcases innerArc_segments_boundary ordered segment member with x | x | y | y
  · exact Or.inl (by simpa [x.1,x.2] using hx)
  · exact Or.inr (Or.inl (by simpa [x.1,x.2] using hx))
  · exact Or.inr (Or.inr (Or.inl (by simpa [y.1,y.2] using hy)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [y.1,y.2] using hy)))

theorem inner_boundaries_disjoint {width height firstDepth secondDepth : Int}
    (different : firstDepth ≠ secondDepth) {point : ℝ × ℝ}
    (first : InnerBoundary width height firstDepth point)
    (second : InnerBoundary width height secondDepth point) : False := by
  rcases first with ⟨fxlo,fxhi,fylo,fyhi,firstSide⟩
  rcases second with ⟨sxlo,sxhi,sylo,syhi,secondSide⟩
  push_cast at fxhi fyhi sxhi syhi firstSide secondSide
  rcases lt_or_gt_of_ne different with order | order
  · have realOrder : (firstDepth : ℝ) < secondDepth := by exact_mod_cast order
    rcases firstSide with side | side | side | side <;> linarith
  · have realOrder : (secondDepth : ℝ) < firstDepth := by exact_mod_cast order
    rcases secondSide with side | side | side | side <;> linarith

theorem normal_cannot_reach_deeper_boundary {width height firstDepth secondDepth : Int}
    (positive : 0 < firstDepth) (deeper : firstDepth < secondDepth) (port : Port) {point : ℝ × ℝ}
    (normalContains : (port.normal width height firstDepth).RealContains point)
    (boundary : InnerBoundary width height secondDepth point) : False := by
  obtain ⟨t,lo,hi,hx,hy⟩ := normalContains
  obtain ⟨side,coordinate⟩ := port
  have realPositive : (0 : ℝ) < firstDepth := by exact_mod_cast positive
  have realDeeper : (firstDepth : ℝ) < secondDepth := by exact_mod_cast deeper
  fin_cases side <;>
    simp [Port.normal,Port.point,Port.innerPoint] at hx hy <;>
    rcases boundary with ⟨xlo,xhi,ylo,yhi,_⟩ <;>
    push_cast at hx hy xhi yhi <;> nlinarith

end LeanTrominoes.OrthogonalBoundaryRouting

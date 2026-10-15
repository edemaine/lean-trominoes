/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryArcNormalContacts
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra

/-! # Separation of arcs at different inward depths -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

set_option maxHeartbeats 2000000

theorem route_image (width height depth : Int) (first second : Port) (point : ℝ × ℝ) :
    GridPolyline.RealContains (route width height depth first second) point ↔
      (first.normal width height depth).RealContains point ∨
      GridPolyline.RealContains (innerArc width height depth first second) point ∨
      (second.normal width height depth).RealContains point := by
  have reverse := GridSegment.realContains_reverse (second.normal width height depth) point
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [route,innerArc,corner,Port.normal,Port.point,Port.innerPoint,
      GridPolyline.RealContains,gridPolylineSegments] <;>
    simp [Port.normal,Port.point,Port.innerPoint,GridSegment.reverse] at reverse <;> tauto

theorem shallow_route_disjoint {width height firstDepth secondDepth margin : Int}
    {first last secondFirst secondLast : Port}
    (firstPositive : 0 < firstDepth) (secondPositive : 0 < secondDepth)
    (firstDepthBound : firstDepth ≤ margin) (secondDepthBound : secondDepth ≤ margin)
    (depthOrder : firstDepth < secondDepth) (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (lastInside : last.Inside width height margin)
    (secondFirstInside : secondFirst.Inside width height margin) (secondLastInside : secondLast.Inside width height margin)
    (firstOrder : first.Before last) (secondOrder : secondFirst.Before secondLast)
    (different : first ≠ secondFirst ∧ first ≠ secondLast ∧ last ≠ secondFirst ∧ last ≠ secondLast)
    (secondFirstOutside : ¬first.Between last secondFirst) (secondLastOutside : ¬first.Between last secondLast)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (route width height firstDepth first last) point)
    (secondContains : GridPolyline.RealContains (route width height secondDepth secondFirst secondLast) point) : False := by
  have firstBoundary := innerArc_real_boundary firstPositive firstDepthBound room firstInside lastInside firstOrder (point := point)
  have secondBoundary := innerArc_real_boundary secondPositive secondDepthBound room secondFirstInside secondLastInside secondOrder (point := point)
  rcases (route_image _ _ _ _ _ _).mp firstContains with firstNormal | firstArc | lastNormal
  · rcases (route_image _ _ _ _ _ _).mp secondContains with secondFirstNormal | secondArc | secondLastNormal
    · exact different.1 (normals_real_contact_eq firstPositive secondPositive firstDepthBound secondDepthBound
        room firstInside secondFirstInside firstNormal secondFirstNormal)
    · exact normal_cannot_reach_deeper_boundary firstPositive depthOrder first firstNormal (secondBoundary secondArc)
    · exact different.2.1 (normals_real_contact_eq firstPositive secondPositive firstDepthBound secondDepthBound
        room firstInside secondLastInside firstNormal secondLastNormal)
  · rcases (route_image _ _ _ _ _ _).mp secondContains with secondFirstNormal | secondArc | secondLastNormal
    · exact secondFirstOutside (normal_innerArc_real_contact_between secondPositive secondDepthBound firstDepthBound
        room firstInside lastInside secondFirstInside firstOrder firstArc secondFirstNormal)
    · exact inner_boundaries_disjoint (by omega) (firstBoundary firstArc) (secondBoundary secondArc)
    · exact secondLastOutside (normal_innerArc_real_contact_between secondPositive secondDepthBound firstDepthBound
        room firstInside lastInside secondLastInside firstOrder firstArc secondLastNormal)
  · rcases (route_image _ _ _ _ _ _).mp secondContains with secondFirstNormal | secondArc | secondLastNormal
    · exact different.2.2.1 (normals_real_contact_eq firstPositive secondPositive firstDepthBound secondDepthBound
        room lastInside secondFirstInside lastNormal secondFirstNormal)
    · exact normal_cannot_reach_deeper_boundary firstPositive depthOrder last lastNormal (secondBoundary secondArc)
    · exact different.2.2.2 (normals_real_contact_eq firstPositive secondPositive firstDepthBound secondDepthBound
        room lastInside secondLastInside lastNormal secondLastNormal)

end LeanTrominoes.OrthogonalBoundaryRouting

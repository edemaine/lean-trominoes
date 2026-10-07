/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcGeometry
import LeanTrominoes.OrthogonalBoundaryPortOrder

/-! # A normal can reach an inner arc only within its boundary interval -/
namespace LeanTrominoes.OrthogonalBoundaryRouting
open PeriodicOrthocrossing

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

theorem Port.normal_axisAligned {width height depth : Int} (positive : 0 < depth) (port : Port) :
    (port.normal width height depth).IsAxisAligned := by
  obtain ⟨side,coordinate⟩ := port
  fin_cases side <;>
    simp [normal,point,innerPoint,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,GridSegment.IsVertical] <;>
    omega

theorem innerArc_orthogonal {width height depth margin : Int} {first second : Port}
    (depthBound : depth ≤ margin) (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) : OrthogonalPolyline (innerArc width height depth first second) := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Before,Port.Inside] at ordered firstInside secondInside <;>
    simp [innerArc,corner,Port.innerPoint,OrthogonalPolyline,
      GridSegment.IsAxisAligned,GridSegment.IsHorizontal,GridSegment.IsVertical] <;> omega

theorem normals_integer_contact_eq {width height firstDepth secondDepth margin : Int} {first second : Port}
    (marginNonnegative : 0 ≤ margin)
    (firstDepthBound : firstDepth ≤ margin) (secondDepthBound : secondDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    {point : Cell} (firstContains : (first.normal width height firstDepth).Contains point)
    (secondContains : (second.normal width height secondDepth).Contains point) : first = second := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  obtain ⟨x,y⟩ := point
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Inside] at firstInside secondInside <;>
    simp [Port.normal,Port.point,Port.innerPoint,GridSegment.Contains,
      GridSegment.IsHorizontal,GridSegment.IsVertical,GridSegment.Between] at firstContains secondContains <;>
    simp <;> omega

theorem normals_real_contact_eq {width height firstDepth secondDepth margin : Int} {first second : Port}
    (firstPositive : 0 < firstDepth) (secondPositive : 0 < secondDepth)
    (firstDepthBound : firstDepth ≤ margin) (secondDepthBound : secondDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    {point : ℝ × ℝ} (firstContains : (first.normal width height firstDepth).RealContains point)
    (secondContains : (second.normal width height secondDepth).RealContains point) : first = second := by
  obtain ⟨point,firstContains,secondContains⟩ := GridSegment.real_intersection_has_integer_witness
    (first.normal_axisAligned firstPositive) (second.normal_axisAligned secondPositive) firstContains secondContains
  exact normals_integer_contact_eq (by omega) firstDepthBound secondDepthBound room firstInside secondInside firstContains secondContains

theorem normal_innerArc_integer_contact_between {width height normalDepth arcDepth margin : Int}
    {first second port : Port} (marginNonnegative : 0 ≤ margin)
    (normalDepthBound : normalDepth ≤ margin) (arcDepthBound : arcDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (portInside : port.Inside width height margin) (ordered : first.Before second)
    {point : Cell} {segment : GridSegment}
    (member : segment ∈ gridPolylineSegments (innerArc width height arcDepth first second))
    (arcContains : segment.Contains point) (normalContains : (port.normal width height normalDepth).Contains point) :
    first.Between second port := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  obtain ⟨portSide,portCoordinate⟩ := port
  obtain ⟨x,y⟩ := point
  fin_cases firstSide <;> fin_cases secondSide <;> fin_cases portSide <;>
    simp [Port.Before,Port.Inside] at ordered firstInside secondInside portInside <;>
    simp [innerArc,corner,Port.innerPoint,gridPolylineSegments] at member <;>
    rcases member with rfl | rfl | rfl | rfl <;>
    simp [Port.normal,Port.point,Port.innerPoint,GridSegment.Contains,
      GridSegment.IsHorizontal,GridSegment.IsVertical,GridSegment.Between] at arcContains normalContains <;>
    simp [Port.Between,Port.Before] <;> omega

theorem normal_innerArc_real_contact_between {width height normalDepth arcDepth margin : Int}
    {first second port : Port} (normalPositive : 0 < normalDepth)
    (normalDepthBound : normalDepth ≤ margin) (arcDepthBound : arcDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (portInside : port.Inside width height margin) (ordered : first.Before second)
    {point : ℝ × ℝ}
    (arcContains : GridPolyline.RealContains (innerArc width height arcDepth first second) point)
    (normalContains : (port.normal width height normalDepth).RealContains point) : first.Between second port := by
  obtain ⟨segment,member,arcContains⟩ := arcContains
  have aligned := (orthogonalPolyline_iff_segments _).mp
    (innerArc_orthogonal arcDepthBound room firstInside secondInside ordered) segment member
  obtain ⟨point,arcContains,normalContains⟩ := GridSegment.real_intersection_has_integer_witness
    aligned (port.normal_axisAligned normalPositive) arcContains normalContains
  exact normal_innerArc_integer_contact_between (by omega) normalDepthBound arcDepthBound room
    firstInside secondInside portInside ordered member arcContains normalContains

end LeanTrominoes.OrthogonalBoundaryRouting

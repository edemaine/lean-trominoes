/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcSeparation

/-! # Boundary arcs stay in their cell and touch its boundary only at ports -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

theorem route_vertex_bounds {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin) :
    ∀ vertex ∈ route width height depth first second,
      0 ≤ vertex.1 ∧ vertex.1 ≤ width ∧ 0 ≤ vertex.2 ∧ vertex.2 ≤ height := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Inside] at firstInside secondInside <;>
    simp [route,innerArc,corner,Port.point,Port.innerPoint] <;> omega

theorem route_real_bounds {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (route width height depth first second) point) :
    (0 : ℝ) ≤ point.1 ∧ point.1 ≤ width ∧ (0 : ℝ) ≤ point.2 ∧ point.2 ≤ height := by
  simpa using GridPolyline.realContains_bounds (route_vertex_bounds positive depthBound room firstInside secondInside) contains

theorem normal_boundary_contact_port {width height depth margin : Int} {port : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height) (inside : port.Inside width height margin)
    {point : ℝ × ℝ} (contains : (port.normal width height depth).RealContains point)
    (boundary : point.1 = 0 ∨ point.1 = (width : ℝ) ∨ point.2 = 0 ∨ point.2 = (height : ℝ)) :
    point = realCell (port.point width height) := by
  obtain ⟨t,lo,hi,hx,hy⟩ := contains
  obtain ⟨side,coordinate⟩ := port
  have realPositive : (0 : ℝ) < depth := by exact_mod_cast positive
  have realBound : (depth : ℝ) ≤ margin := by exact_mod_cast depthBound
  have realRoom : 2*(margin : ℝ) < width ∧ 2*(margin : ℝ) < height := by exact_mod_cast room
  unfold Port.Inside at inside
  have realInside : (margin : ℝ) < coordinate ∧ (coordinate : ℝ) <
      (((if side.val = 0 ∨ side.val = 2 then height else width)-margin : Int) : ℝ) := by exact_mod_cast inside
  fin_cases side <;> simp at realInside
  all_goals
    have realCoordinateLo : (margin : ℝ) < coordinate := by exact_mod_cast realInside.1
    simp [Port.normal,Port.point,Port.innerPoint] at hx hy
    push_cast at hx hy realInside
    rcases boundary with on | on | on | on
    all_goals apply Prod.ext <;> simp [realCell,Port.point] <;> nlinarith

theorem route_boundary_contact_ports {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (route width height depth first second) point)
    (boundary : point.1 = 0 ∨ point.1 = (width : ℝ) ∨ point.2 = 0 ∨ point.2 = (height : ℝ)) :
    point = realCell (first.point width height) ∨ point = realCell (second.point width height) := by
  rcases (route_image _ _ _ _ _ _).mp contains with firstNormal | arc | secondNormal
  · exact Or.inl (normal_boundary_contact_port positive depthBound room firstInside firstNormal boundary)
  · have bounds := innerArc_real_boundary positive depthBound room firstInside secondInside ordered arc
    have realPositive : (0 : ℝ) < depth := by exact_mod_cast positive
    rcases bounds with ⟨xlo,xhi,ylo,yhi,_⟩
    push_cast at xhi yhi
    rcases boundary with on | on | on | on <;> exfalso <;> linarith
  · exact Or.inr (normal_boundary_contact_port positive depthBound room secondInside secondNormal boundary)

end LeanTrominoes.OrthogonalBoundaryRouting

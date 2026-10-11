/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanPlacement
import LeanTrominoes.OrthogonalBendFanBoundaryLocality

/-! # Assigned fans respect parent rectangles through their actual vertex stars

Original vertices have an integer margin. At inserted boundary bends, all
actual incident rays must point into the parent rectangle's half planes.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanRoute_inside_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (portMember : port ∈ allPorts (subdivisionGraph source drawing)) {center point : Cell} {left right bottom top factor : Int}
    (spacing : 10 ≤ factor) (inside : left ≤ center.1 ∧ center.1 ≤ right ∧ bottom ≤ center.2 ∧ center.2 ≤ top)
    (originalMargin : ∀ value, port.vertex = .original value → left < center.1 ∧ center.1 < right ∧ bottom < center.2 ∧ center.2 < top)
    (leftSide : center.1 = left → ∀ other ∈ portsAt (subdivisionGraph source drawing) port.vertex,
      0 ≤ BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey other))
    (rightSide : center.1 = right → ∀ other ∈ portsAt (subdivisionGraph source drawing) port.vertex,
      BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey other) ≤ 0)
    (bottomSide : center.2 = bottom → ∀ other ∈ portsAt (subdivisionGraph source drawing) port.vertex,
      0 ≤ BendFan.verticalSign ((shiftedDrawing source drawing).portRayKey other))
    (topSide : center.2 = top → ∀ other ∈ portsAt (subdivisionGraph source drawing) port.vertex,
      BendFan.verticalSign ((shiftedDrawing source drawing).portRayKey other) ≤ 0)
    (member : point ∈ fanRoute source drawing port) :
    factor*left ≤ factor*center.1+point.1 ∧ factor*center.1+point.1 ≤ factor*right ∧
      factor*bottom ≤ factor*center.2+point.2 ∧ factor*center.2+point.2 ≤ factor*top := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) portMember
  cases vertex : port.vertex with
  | original value =>
      have margin := originalMargin value vertex
      have bounds := fanRoute_bounds source drawing port point member
      have horizontal := BendFan.scaled_coordinate_inside spacing ⟨inside.1,inside.2.1⟩
        (abs_le.mpr ⟨by omega,by omega⟩ : |point.1| ≤ 10)
        (fun _ => by omega) (fun _ => by omega)
      have vertical := BendFan.scaled_coordinate_inside spacing ⟨inside.2.2.1,inside.2.2.2⟩
        (abs_le.mpr ⟨bounds.2.2.1,bounds.2.2.2⟩)
        (fun _ => by omega) (fun _ => by omega)
      exact ⟨horizontal.1,horizontal.2,vertical.1,vertical.2⟩
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember leftSide rightSide bottomSide topSide
      have ports := bend_ports_eq vertexMember
      have firstMember : bendFirstPort source drawing edgeIndex pointIndex ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        rw [ports]; simp
      have secondMember : bendSecondPort source drawing edgeIndex pointIndex ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        rw [ports]; simp
      apply BendFan.assignedProfile_scaled_inside_rectangle (bend_keys_ne planar vertexMember)
        (bendPortIndex source drawing edgeIndex pointIndex port) spacing inside
      · intro boundary
        exact ⟨leftSide boundary _ firstMember,leftSide boundary _ secondMember⟩
      · intro boundary
        exact ⟨rightSide boundary _ firstMember,rightSide boundary _ secondMember⟩
      · intro boundary
        exact ⟨bottomSide boundary _ firstMember,bottomSide boundary _ secondMember⟩
      · intro boundary
        exact ⟨topSide boundary _ firstMember,topSide boundary _ secondMember⟩
      · simpa only [fanRoute,vertex,bendProfile] using member

theorem fanAt_points_inside_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {center : Cell} {left right bottom top factor : Int} (raster : Nat)
    (fanInside : ∀ point ∈ fanRoute source drawing port,
      factor*left ≤ factor*center.1+point.1 ∧ factor*center.1+point.1 ≤ factor*right ∧
        factor*bottom ≤ factor*center.2+point.2 ∧ factor*center.2+point.2 ≤ factor*top) :
    ∀ point ∈ fanAt source drawing factor raster center port,
      (raster : Int)*factor*left ≤ point.1 ∧ point.1 ≤ (raster : Int)*factor*right ∧
        (raster : Int)*factor*bottom ≤ point.2 ∧ point.2 ≤ (raster : Int)*factor*top := by
  intro point member
  obtain ⟨scaled,scaledMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp scaledMember
  have bounds := fanInside original originalMember
  have nonnegative : (0 : Int) ≤ raster := by positivity
  simp only [Cell.add,Cell.scale]
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left bounds.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.2.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.2.2 nonnegative]⟩

theorem fanAt_real_inside_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {center : Cell} {left right bottom top factor : Int} (raster : Nat)
    (fanInside : ∀ point ∈ fanRoute source drawing port,
      factor*left ≤ factor*center.1+point.1 ∧ factor*center.1+point.1 ≤ factor*right ∧
        factor*bottom ≤ factor*center.2+point.2 ∧ factor*center.2+point.2 ≤ factor*top)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (fanAt source drawing factor raster center port) point) :
    (raster : ℝ)*factor*left ≤ point.1 ∧ point.1 ≤ (raster : ℝ)*factor*right ∧
      (raster : ℝ)*factor*bottom ≤ point.2 ∧ point.2 ≤ (raster : ℝ)*factor*top := by
  have bounds := GridPolyline.realContains_bounds (fanAt_points_inside_rectangle raster fanInside) contains
  push_cast at bounds
  exact bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendRayKeys
import LeanTrominoes.PeriodicGridDrawingRawBendDirectionBounds
import LeanTrominoes.OrthogonalCubicRefinementBounds

/-! # Certified digital cores for every edge of the raw subdivision

The selected spacing factors give simple orthogonal cores with exact anchor
endpoints, endpoint rectangle bounds, and a tube of radius `10L + 3` around
the original piece. Nonincident original pieces yield disjoint cores.
-/
namespace LeanTrominoes.GridSegment

theorem bounded_coordinate_sign {radius factor original output : Int} (small : |output-factor*original| ≤ radius)
    (radiusNonnegative : 0 ≤ radius) (spacing : radius < factor) (nonzero : original ≠ 0) :
    if 0 < original then 0 < output else output < 0 := by
  have factorPositive : 0 < factor := by omega
  have bounds := abs_le.mp small
  split_ifs with positive
  · have product := mul_le_mul_of_nonneg_left (show 1 ≤ original by omega) factorPositive.le
    nlinarith
  · have product := mul_le_mul_of_nonneg_left (show original ≤ -1 by omega) factorPositive.le
    nlinarith

theorem BoundedEndpointPerturbation.nonconstant {radius factor : Int} {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original output)
    (radiusNonnegative : 0 ≤ radius) (spacing : 2*radius < factor)
    (different : original.start ≠ original.finish) : output.start ≠ output.finish := by
  have genuine : original.direction.1 ≠ 0 ∨ original.direction.2 ≠ 0 := by
    by_contra zero
    simp only [not_or,not_not] at zero
    apply different
    simp only [GridSegment.direction] at zero
    apply Prod.ext <;> omega
  intro equal
  rcases genuine with horizontal | vertical
  · have sign := bounded_coordinate_sign perturbed.direction.1 (by omega) spacing horizontal
    simp only [GridSegment.direction,equal,sub_self,lt_self_iff_false,ite_self] at sign
  · have sign := bounded_coordinate_sign perturbed.direction.2 (by omega) spacing vertical
    simp only [GridSegment.direction,equal,sub_self,lt_self_iff_false,ite_self] at sign

end LeanTrominoes.GridSegment
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

def cubicCore {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : GridSegment :=
  (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) tagged).scale (Cubic.rasterFactor drawing.gridSize)

def coreSide {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : Int :=
  if 0 < (subdivisionSegment source drawing tagged.1).direction.1 then 1 else -1

theorem coreSide_unit {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : coreSide source drawing tagged = 1 ∨ coreSide source drawing tagged = -1 := by
  unfold coreSide
  split_ifs <;> simp

noncomputable def coreRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : List Cell :=
  if (subdivisionSegment source drawing tagged.1).direction.1 = 0 then (cubicCore source drawing tagged).digitalRoute
  else (cubicCore source drawing tagged).kickedDigitalRoute (coreSide source drawing tagged)

theorem cubicCore_nonconstant {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (cubicCore source drawing tagged).start ≠ (cubicCore source drawing tagged).finish := by
  have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize
  have different := (anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) tagged).nonconstant
    (by norm_num) (by omega) (subdivision_segment_nonconstant planar member)
  intro equal
  exact different (Cell.scale_injective
    (by exact_mod_cast (Cubic.rasterFactor_positive drawing.gridSize).ne') equal)

theorem cubicCore_horizontal_width {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) :
    3 ≤ coreSide source drawing tagged*((cubicCore source drawing tagged).finish.1-(cubicCore source drawing tagged).start.1) := by
  have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize
  have sign := GridSegment.bounded_coordinate_sign
    (anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) tagged).direction.1
    (by norm_num) (by omega) horizontal
  have rasterLarge : (3 : Int) ≤ Cubic.rasterFactor drawing.gridSize := by
    simp only [Cubic.rasterFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    omega
  change 3 ≤ coreSide source drawing tagged*(cubicCore source drawing tagged).direction.1
  simp only [cubicCore,GridSegment.direction_scale,Cell.scale,coreSide]
  split_ifs with rightward
  · rw [if_pos rightward] at sign
    have product := mul_le_mul_of_nonneg_left (show 1 ≤ (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) tagged).direction.1 by omega)
      (by omega : 0 ≤ (Cubic.rasterFactor drawing.gridSize : Int))
    nlinarith
  · rw [if_neg rightward] at sign
    have product := mul_le_mul_of_nonneg_left (show (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) tagged).direction.1 ≤ -1 by omega)
      (by omega : 0 ≤ (Cubic.rasterFactor drawing.gridSize : Int))
    nlinarith

theorem coreRoute_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (coreRoute source drawing tagged).head? = some (cubicCore source drawing tagged).start ∧
      (coreRoute source drawing tagged).getLast? = some (cubicCore source drawing tagged).finish := by
  have nonzero : coreSide source drawing tagged ≠ 0 := by
    rcases coreSide_unit source drawing tagged with equal | equal <;> omega
  unfold coreRoute
  split_ifs
  · exact ⟨GridSegment.digitalRoute_head _,GridSegment.digitalRoute_last _⟩
  · exact ⟨GridSegment.kickedDigitalRoute_head _ nonzero,GridSegment.kickedDigitalRoute_last _ nonzero⟩

theorem coreRoute_orthogonal {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : PeriodicOrthocrossing.OrthogonalPolyline (coreRoute source drawing tagged) := by
  unfold coreRoute
  split_ifs
  · exact GridSegment.digitalRoute_orthogonal _
  · exact GridSegment.kickedDigitalRoute_orthogonal _
      (by rcases coreSide_unit source drawing tagged with equal | equal <;> omega)

theorem coreRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) : GridPolyline.IsRealOpenSimple (coreRoute source drawing tagged) := by
  unfold coreRoute
  split_ifs
  · exact GridSegment.digitalRoute_simple (cubicCore_nonconstant planar member)
  · exact GridSegment.kickedDigitalRoute_simple
      (by rcases coreSide_unit source drawing tagged with equal | equal <;> omega) (cubicCore_nonconstant planar member)

theorem coreRoute_box {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    (cubicCore source drawing tagged).RealBoxContains point := by
  unfold coreRoute at contains
  split_ifs at contains with vertical
  · exact GridSegment.digitalRoute_box _ contains
  · exact GridSegment.kickedDigitalRoute_box (coreSide_unit source drawing tagged)
      (cubicCore_horizontal_width source drawing tagged vertical) contains

theorem coreRoute_tube {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    ((subdivisionSegment source drawing tagged.1).scale
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))).RealTubeContains
      ((Cubic.rasterFactor drawing.gridSize : ℝ)*10+3) point := by
  have positive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have perturbed := anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) tagged
  unfold coreRoute at contains
  split_ifs at contains
  · exact (perturbed.digitalRoute_tube positive contains).mono (by norm_num)
  · exact perturbed.kickedDigitalRoute_tube positive (coreSide_unit source drawing tagged) contains

theorem coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (disjoint : ∀ point : ℝ × ℝ, (subdivisionSegment source drawing first.1).RealContains point →
      ¬(subdivisionSegment source drawing second.1).RealContains point)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (coreRoute source drawing first) point) :
    ¬GridPolyline.RealContains (coreRoute source drawing second) point := by
  intro secondContains
  have firstBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal firstMember
  have secondBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal secondMember
  have gridPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have realRasterPositive : (0 : ℝ) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast rasterPositive
  have rasterAtLeastOne : (1 : ℝ) ≤ Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast (show 1 ≤ (Cubic.rasterFactor drawing.gridSize : Int) by omega)
  have spacing : 4*(2*(drawing.gridSize : ℝ))*((Cubic.rasterFactor drawing.gridSize : ℝ)*10+3) <
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int) : Int) := by
    have base : 4*(2*(drawing.gridSize : ℝ))*(10+3) < (Cubic.coreFactor drawing.gridSize : ℝ) := by
      exact_mod_cast Cubic.coreFactor_tube_spacing drawing.gridSize
    have scaled := mul_lt_mul_of_pos_left base realRasterPositive
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ drawing.gridSize by positivity) (sub_nonneg.mpr rasterAtLeastOne)]
  exact GridSegment.scaled_tubes_disjoint (by omega) (by positivity) (by simpa using spacing)
    firstBounds secondBounds disjoint point (coreRoute_tube source drawing first firstContains)
    (coreRoute_tube source drawing second secondContains)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

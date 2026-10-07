/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreVerticalContacts

/-! # A boundary detour cannot meet another protoedge's horizontal track -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem horizontal_boundary_contacts_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {horizontalTagged boundaryTagged : PeriodicEdge Vertex × Nat}
    (horizontalEdgeMember : horizontalTagged ∈ graph.edges.zipIdx) (boundaryEdgeMember : boundaryTagged ∈ graph.edges.zipIdx)
    {horizontalPiece boundaryPiece : ClassifiedSegment Vertex}
    (horizontalMember : horizontalPiece ∈ classifiedCore graph horizontalTagged.1 horizontalTagged.2)
    (boundaryMember : boundaryPiece ∈ classifiedCore graph boundaryTagged.1 boundaryTagged.2)
    (horizontal : horizontalPiece.segment.IsHorizontal)
    (boundary : boundaryPiece.role = .boundaryVertical boundaryTagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (horizontalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (boundaryPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    horizontalTagged.2 = boundaryTagged.2 := by
  have role := classifiedCore_horizontal_role graph horizontalTagged.1 horizontalTagged.2 horizontalPiece horizontalMember horizontal
  have fixed := GridSegment.realContains_horizontal_y ((GridSegment.isHorizontal_translate _ _).mpr horizontal) firstContains
  change point.2 = (((drawingGridSize graph : Int)*firstCell.2+horizontalPiece.segment.start.2 : Int) : ℝ) at fixed
  rw [classifiedCore_horizontal_lane graph horizontalTagged.1 horizontalTagged.2 horizontalPiece horizontalMember role] at fixed
  push_cast at fixed
  have horizontalBounds := classifiedCore_horizontal_lane_bounds horizontalEdgeMember horizontalMember role
  have boundaryBounds := edgeTrack_bounds graph boundaryEdgeMember
  have ends := classifiedCore_boundary_bounds graph boundaryTagged.1 boundaryTagged.2 boundaryPiece boundaryMember boundary
  have box := GridSegment.realBoxContains_of_realContains secondContains
  simp only [GridSegment.RealBoxContains,GridSegment.translate,Cell.scale,Cell.add,
    min_add_add_left,max_add_add_left,Int.cast_add,Int.cast_mul] at box
  rw [ends.1,ends.2,min_eq_left (by omega : edgeTrack boundaryTagged.2 ≤ edgeTrack boundaryTagged.2+1),
    max_eq_right (by omega : edgeTrack boundaryTagged.2 ≤ edgeTrack boundaryTagged.2+1)] at box
  simp only [Int.cast_natCast,Int.cast_add,Int.cast_one] at box
  have firstBand : (horizontalLaneBase horizontalPiece.role : ℝ)+(drawingGridSize graph : ℝ)*
        (horizontalLaneCellShift horizontalTagged.1 horizontalPiece.role+firstCell.2 : Int) ≤ point.2 ∧
      point.2 ≤ (horizontalLaneBase horizontalPiece.role : ℝ)+(drawingGridSize graph : ℝ)*
        (horizontalLaneCellShift horizontalTagged.1 horizontalPiece.role+firstCell.2 : Int) := by
    push_cast
    constructor <;> nlinarith [fixed]
  have secondBand : (edgeTrack boundaryTagged.2 : ℝ)+(drawingGridSize graph : ℝ)*secondCell.2 ≤ point.2 ∧
      point.2 ≤ (edgeTrack boundaryTagged.2+1 : Int)+(drawingGridSize graph : ℝ)*secondCell.2 := by
    push_cast
    exact ⟨by linarith [box.2.2.1],by linarith [box.2.2.2]⟩
  have shifts := GridSegment.normalized_bands_periodic_shifts_unique (point := point.2)
    (by exact_mod_cast drawingGridSize_pos graph) horizontalBounds
    (by omega : (0 : Int) ≤ edgeTrack boundaryTagged.2 ∧ edgeTrack boundaryTagged.2+1 < drawingGridSize graph)
    firstBand secondBand
  rw [shifts] at firstBand
  have lower : edgeTrack boundaryTagged.2 ≤ horizontalLaneBase horizontalPiece.role := by
    exact_mod_cast (by linarith [secondBand.1,firstBand.2] :
      (edgeTrack boundaryTagged.2 : ℝ) ≤ horizontalLaneBase horizontalPiece.role)
  have upper : horizontalLaneBase horizontalPiece.role ≤ edgeTrack boundaryTagged.2+1 := by
    exact_mod_cast (by linarith [firstBand.1,secondBand.2] :
      (horizontalLaneBase horizontalPiece.role : ℝ) ≤ (edgeTrack boundaryTagged.2+1 : Int))
  rcases classifiedCore_horizontal_low_or_high graph horizontalTagged.1 horizontalTagged.2 horizontalPiece horizontalMember role with low | high
  · rw [low] at lower upper
    simp only [horizontalLaneBase,edgeTrack] at lower upper
    omega
  · rw [high] at lower upper
    simp only [horizontalLaneBase,edgeTrack] at lower upper
    omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreEndpointRows

/-! # A private horizontal track cannot pass through another edge's bend -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem private_row_contact_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {horizontalTagged rowTagged : PeriodicEdge Vertex × Nat}
    (horizontalEdgeMember : horizontalTagged ∈ graph.edges.zipIdx) (rowEdgeMember : rowTagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph horizontalTagged.1 horizontalTagged.2)
    (horizontal : piece.role.IsHorizontalRole) {y firstShift secondShift : Int}
    (row : CoreRow graph rowTagged.2 y)
    (equal : horizontalLaneBase piece.role+(drawingGridSize graph : Int)*firstShift =
      y+(drawingGridSize graph : Int)*secondShift) : horizontalTagged.2 = rowTagged.2 := by
  have pieceBounds := classifiedCore_horizontal_lane_bounds horizontalEdgeMember pieceMember horizontal
  have rowBounds := edgeTrack_bounds graph rowEdgeMember
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have gridThree : (3 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  obtain ⟨shift,portRow | lowRow | highRow⟩ := row
  · rw [portRow] at equal
    have normalized : horizontalLaneBase piece.role+(drawingGridSize graph : Int)*firstShift =
        3+(drawingGridSize graph : Int)*(shift+secondShift) := by linear_combination equal
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega : (0 : Int) ≤ 3 ∧ (3 : Int) < drawingGridSize graph) normalized
    rcases classifiedCore_horizontal_low_or_high graph horizontalTagged.1 horizontalTagged.2 piece pieceMember horizontal with low | high
    · rw [low] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega
    · rw [high] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega
  · rw [lowRow] at equal
    have normalized : horizontalLaneBase piece.role+(drawingGridSize graph : Int)*firstShift =
        edgeTrack rowTagged.2+(drawingGridSize graph : Int)*(shift+secondShift) := by linear_combination equal
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega : (0 : Int) ≤ edgeTrack rowTagged.2 ∧ edgeTrack rowTagged.2 < drawingGridSize graph) normalized
    rcases classifiedCore_horizontal_low_or_high graph horizontalTagged.1 horizontalTagged.2 piece pieceMember horizontal with low | high
    · rw [low] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega
    · rw [high] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega
  · rw [highRow] at equal
    have normalized : horizontalLaneBase piece.role+(drawingGridSize graph : Int)*firstShift =
        edgeTrack rowTagged.2+1+(drawingGridSize graph : Int)*(shift+secondShift) := by linear_combination equal
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega : (0 : Int) ≤ edgeTrack rowTagged.2+1 ∧ edgeTrack rowTagged.2+1 < drawingGridSize graph) normalized
    rcases classifiedCore_horizontal_low_or_high graph horizontalTagged.1 horizontalTagged.2 piece pieceMember horizontal with low | high
    · rw [low] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega
    · rw [high] at lanes
      simp only [horizontalLaneBase,edgeTrack] at lanes
      omega

theorem horizontal_endpoint_contact_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {horizontalTagged rowTagged : PeriodicEdge Vertex × Nat}
    (horizontalEdgeMember : horizontalTagged ∈ graph.edges.zipIdx) (rowEdgeMember : rowTagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph horizontalTagged.1 horizontalTagged.2)
    (horizontal : piece.segment.IsHorizontal) {endpoint : Cell}
    (row : CoreRow graph rowTagged.2 endpoint.2) (firstCell secondCell : Cell)
    (contains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint))) :
    horizontalTagged.2 = rowTagged.2 := by
  have role := classifiedCore_horizontal_role graph horizontalTagged.1 horizontalTagged.2 piece pieceMember horizontal
  have fixed := GridSegment.realContains_horizontal_y ((GridSegment.isHorizontal_translate _ _).mpr horizontal) contains
  change ((Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).2 : ℝ) =
    ((piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.2 : ℝ) at fixed
  have fixedInt : (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).2 =
      (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.2 := by
    exact_mod_cast fixed
  change (drawingGridSize graph : Int)*secondCell.2+endpoint.2 =
    (drawingGridSize graph : Int)*firstCell.2+piece.segment.start.2 at fixedInt
  rw [classifiedCore_horizontal_lane graph horizontalTagged.1 horizontalTagged.2 piece pieceMember role] at fixedInt
  apply private_row_contact_index horizontalEdgeMember rowEdgeMember pieceMember role row
    (firstShift := horizontalLaneCellShift horizontalTagged.1 piece.role+firstCell.2) (secondShift := secondCell.2)
  linear_combination -fixedInt

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

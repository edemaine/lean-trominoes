/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralFanSimple
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreHorizontalContacts

/-! # Fans avoid private horizontal rows and columns outside their vertex block -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan classifiedCore core

theorem fan_horizontal_core_disjoint {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) {fanPort : GraphPort Vertex} (fanMember : fanPort ∈ allPorts graph)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    (horizontal : piece.segment.IsHorizontal) {fanCell coreCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell) (fan graph orthogonal fanPort)) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains point) : False := by
  have fanImage := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have box := fan_real_block_bounds orthogonal fanMember fanImage
  simp only [Cell.scale,Prod.snd,Int.cast_mul,Int.cast_natCast] at box
  have fanBand : ((1 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 ≤ point.2 ∧
      point.2 ≤ ((3 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 := by
    norm_num only [Int.cast_ofNat]
    exact ⟨by linarith [box.2.2.1],by linarith [box.2.2.2]⟩
  have role := classifiedCore_horizontal_role graph tagged.1 tagged.2 piece pieceMember horizontal
  have fixed := GridSegment.realContains_horizontal_y ((GridSegment.isHorizontal_translate _ _).mpr horizontal) coreContains
  change point.2 = (((drawingGridSize graph : Int)*coreCell.2+piece.segment.start.2 : Int) : ℝ) at fixed
  rw [classifiedCore_horizontal_lane graph tagged.1 tagged.2 piece pieceMember role] at fixed
  push_cast at fixed
  have coreBand : (horizontalLaneBase piece.role : ℝ)+(drawingGridSize graph : ℝ)*
        (coreCell.2+horizontalLaneCellShift tagged.1 piece.role : Int) ≤ point.2 ∧
      point.2 ≤ (horizontalLaneBase piece.role : ℝ)+(drawingGridSize graph : ℝ)*
        (coreCell.2+horizontalLaneCellShift tagged.1 piece.role : Int) := by
    push_cast
    constructor <;> nlinarith [fixed]
  have above : (3 : Int) < horizontalLaneBase piece.role := by
    rcases classifiedCore_horizontal_low_or_high graph tagged.1 tagged.2 piece pieceMember role with low | high
    · rw [low]
      simp only [horizontalLaneBase,edgeTrack]
      omega
    · rw [high]
      simp only [horizontalLaneBase,edgeTrack]
      omega
  have gridThree : (3 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  exact GridSegment.normalized_bands_disjoint (point := point.2) (by exact_mod_cast drawingGridSize_pos graph)
    (by omega : (0 : Int) ≤ 1 ∧ (3 : Int) < drawingGridSize graph)
    (classifiedCore_horizontal_lane_bounds edgeMember pieceMember role) (Or.inl above) fanBand coreBand

theorem fan_outside_vertical_column_disjoint {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {fanPort : GraphPort Vertex} (fanMember : fanPort ∈ allPorts graph)
    {segment : GridSegment} (vertical : segment.IsVertical) {base storedShift : Int}
    (normalized : 0 ≤ base ∧ base < drawingGridSize graph)
    (outside : fanBlockFinish graph fanPort.vertex < base ∨ base < fanBlockStart graph fanPort.vertex)
    (column : segment.start.1 = base+(drawingGridSize graph : Int)*storedShift)
    {fanCell coreCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell) (fan graph orthogonal fanPort)) point)
    (coreContains : (segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains point) : False := by
  have fanImage := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have box := fan_real_block_bounds orthogonal fanMember fanImage
  have block := fan_block_bounds wellFormed fanMember
  simp only [Cell.scale,Prod.fst,Int.cast_mul,Int.cast_natCast] at box
  have fanBand : (fanBlockStart graph fanPort.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 ≤ point.1 ∧
      point.1 ≤ (fanBlockFinish graph fanPort.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 :=
    ⟨by linarith [box.1],by linarith [box.2.1]⟩
  have fixed := GridSegment.realContains_vertical_x ((GridSegment.isVertical_translate _ _).mpr vertical) coreContains
  change point.1 = (((drawingGridSize graph : Int)*coreCell.1+segment.start.1 : Int) : ℝ) at fixed
  rw [column] at fixed
  push_cast at fixed
  have coreBand : (base : ℝ)+(drawingGridSize graph : ℝ)*(coreCell.1+storedShift : Int) ≤ point.1 ∧
      point.1 ≤ (base : ℝ)+(drawingGridSize graph : ℝ)*(coreCell.1+storedShift : Int) := by
    push_cast
    constructor <;> nlinarith [fixed]
  exact GridSegment.normalized_bands_disjoint (point := point.1) (by exact_mod_cast drawingGridSize_pos graph)
    (by omega : 0 ≤ fanBlockStart graph fanPort.vertex ∧ fanBlockFinish graph fanPort.vertex < drawingGridSize graph)
    normalized outside fanBand coreBand

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

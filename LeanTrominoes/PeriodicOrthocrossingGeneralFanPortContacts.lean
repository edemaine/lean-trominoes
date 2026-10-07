/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralFanSimple
import LeanTrominoes.PeriodicOrthocrossingGeneralCorePortBands
import LeanTrominoes.GridSegmentRealAxisCoordinates

/-! # A fan can meet a port spine only at their common port -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan classifiedCore core

theorem fan_port_spine_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {fanPort : GraphPort Vertex} (fanMember : fanPort ∈ allPorts graph)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    (vertical : piece.segment.IsVertical) {spinePort : GraphPort Vertex}
    (spine : piece.role.activeVerticalPort = some spinePort)
    {fanCell coreCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell) (fan graph orthogonal fanPort)) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains point) :
    fanPort = spinePort ∧ fanCell = Cell.add coreCell (corePortShift tagged.1 piece.role) ∧
      point = realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) fanCell) (portX graph fanPort,3)) := by
  have fanImage := (GridPolyline.realContains_translate_inverse _ _ _).mp fanContains
  have fanBox := fan_real_block_bounds orthogonal fanMember fanImage
  have fanBlock := fan_block_bounds wellFormed fanMember
  have portMember := classifiedCore_activePort_mem edgeMember piece pieceMember spinePort spine
  have portBounds := portX_lt_gridSize wellFormed portMember
  have tracks := edgeTrack_bounds graph edgeMember
  have band := core_port_spine_band graph tagged.1 tagged.2 edgeLocal piece pieceMember spinePort spine
  have fixed := GridSegment.realContains_vertical_x ((GridSegment.isVertical_translate _ _).mpr vertical) coreContains
  change point.1 = (((drawingGridSize graph : Int)*coreCell.1+piece.segment.start.1 : Int) : ℝ) at fixed
  rw [band.1] at fixed
  push_cast at fixed
  have coreBox := GridSegment.realBoxContains_of_realContains coreContains
  simp only [GridSegment.RealBoxContains,GridSegment.translate,Cell.scale,Cell.add,
    min_add_add_left,max_add_add_left,Int.cast_add,Int.cast_mul,Int.cast_natCast] at coreBox
  have lo : (3 : ℝ)+(drawingGridSize graph : ℝ)*(corePortShift tagged.1 piece.role).2 ≤
      (min piece.segment.start.2 piece.segment.finish.2 : Int) := by exact_mod_cast band.2.1
  have hi : (max piece.segment.start.2 piece.segment.finish.2 : Int) ≤
      (edgeTrack tagged.2+1 : Int)+(drawingGridSize graph : ℝ)*(corePortShift tagged.1 piece.role).2 := by exact_mod_cast band.2.2
  push_cast at lo hi
  simp only [Int.cast_min,Int.cast_max] at coreBox
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul,Int.cast_natCast] at fanBox
  have fanX : (fanBlockStart graph fanPort.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 ≤ point.1 ∧
      point.1 ≤ (fanBlockFinish graph fanPort.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 :=
    ⟨by linarith [fanBox.1],by linarith [fanBox.2.1]⟩
  have coreX : (portX graph spinePort : ℝ)+(drawingGridSize graph : ℝ)*
        (coreCell.1+(corePortShift tagged.1 piece.role).1 : Int) ≤ point.1 ∧
      point.1 ≤ (portX graph spinePort : ℝ)+(drawingGridSize graph : ℝ)*
        (coreCell.1+(corePortShift tagged.1 piece.role).1 : Int) := by
    push_cast
    constructor <;> nlinarith [fixed]
  have fanY : ((1 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 ≤ point.2 ∧
      point.2 ≤ ((3 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 := by
    norm_num only [Int.cast_ofNat]
    exact ⟨by linarith [fanBox.2.2.1],by linarith [fanBox.2.2.2]⟩
  have coreY : ((3 : Int) : ℝ)+(drawingGridSize graph : ℝ)*
        (coreCell.2+(corePortShift tagged.1 piece.role).2 : Int) ≤ point.2 ∧
      point.2 ≤ (edgeTrack tagged.2+1 : Int)+(drawingGridSize graph : ℝ)*
        (coreCell.2+(corePortShift tagged.1 piece.role).2 : Int) := by
    push_cast
    norm_num only [Int.cast_ofNat]
    exact ⟨by nlinarith [coreBox.2.2.1,lo],by nlinarith [coreBox.2.2.2,hi]⟩
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have xShifts := GridSegment.normalized_bands_periodic_shifts_unique (point := point.1) gridPositive
    (by omega : 0 ≤ fanBlockStart graph fanPort.vertex ∧ fanBlockFinish graph fanPort.vertex < drawingGridSize graph)
    (by omega : 0 ≤ portX graph spinePort ∧ portX graph spinePort < drawingGridSize graph) fanX coreX
  have yShifts := GridSegment.normalized_bands_periodic_shifts_unique (point := point.2) gridPositive
    (by omega : (0 : Int) ≤ 1 ∧ (3 : Int) < drawingGridSize graph)
    (by omega : (0 : Int) ≤ 3 ∧ edgeTrack tagged.2+1 < drawingGridSize graph) fanY coreY
  have cells : fanCell = Cell.add coreCell (corePortShift tagged.1 piece.role) := Prod.ext xShifts yShifts
  norm_num only [Int.cast_ofNat] at fanY coreY
  have top : (point.1-(Cell.scale (drawingGridSize graph : Int) fanCell).1,
      point.2-(Cell.scale (drawingGridSize graph : Int) fanCell).2).2 = (3 : ℝ) := by
    rw [← yShifts] at coreY
    simp only [Cell.scale,Prod.snd,Int.cast_mul,Int.cast_natCast]
    linarith [coreY.1,fanY.2]
  have contact := fan_top_contact orthogonal fanMember degree fanImage top
  have cx := congrArg Prod.fst contact
  have cy := congrArg Prod.snd contact
  simp only [realCell,Cell.scale,Prod.fst,Prod.snd,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat] at cx cy
  have columns : portX graph fanPort = portX graph spinePort := by
    rw [xShifts] at cx
    push_cast at cx
    exact_mod_cast (by nlinarith [cx,fixed] : (portX graph fanPort : ℝ) = portX graph spinePort)
  refine ⟨portX_injective wellFormed fanMember portMember columns,cells,?_⟩
  apply Prod.ext <;> simp only [realCell,Cell.add,Cell.scale,Prod.fst,Prod.snd,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat] <;> linarith

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

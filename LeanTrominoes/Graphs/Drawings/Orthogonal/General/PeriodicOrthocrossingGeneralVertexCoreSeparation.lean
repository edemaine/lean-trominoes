/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralVertexBounds
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreOccurrenceCrossings

/-! # No vertex center belongs to any track core -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem indexed_vertex_core_disjoint {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {index : Nat} (valid : index < graph.vertices.length)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    (vertexCell coreCell : Cell) :
    ¬(piece.segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) vertexCell) (position graph index))) := by
  intro contains
  let point := realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) vertexCell) (position graph index))
  change (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains point at contains
  have vertexBounds := indexed_vertex_bounds wellFormed valid
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have gridTwo : (2 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  have px : point.1 = ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 := by
    simp [point,realCell,Cell.add,Cell.scale,add_comm]
  have py : point.2 = ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 := by
    simp [point,realCell,position,Cell.add,Cell.scale,add_comm]
  have vertexXBand : ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 ≤ point.1 ∧
      point.1 ≤ ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 := ⟨px.ge,px.le⟩
  have vertexYBand : ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 ≤ point.2 ∧
      point.2 ≤ ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 := ⟨py.ge,py.le⟩
  have axis : piece.segment.IsAxisAligned := by
    apply (orthogonalPolyline_iff_segments _).mp (core_orthogonal wellFormed member edgeLocal)
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩
  rcases axis with horizontal | vertical
  · have role := classifiedCore_horizontal_role graph tagged.1 tagged.2 piece pieceMember horizontal
    have fixed := GridSegment.realContains_horizontal_y ((GridSegment.isHorizontal_translate _ _).mpr horizontal) contains
    change point.2 = (((drawingGridSize graph : Int)*coreCell.2+piece.segment.start.2 : Int) : ℝ) at fixed
    rw [classifiedCore_horizontal_lane graph tagged.1 tagged.2 piece pieceMember role] at fixed
    push_cast at fixed
    have band : (horizontalLaneBase piece.role : ℝ)+(drawingGridSize graph : ℝ)*
          (coreCell.2+horizontalLaneCellShift tagged.1 piece.role : Int) ≤ point.2 ∧
        point.2 ≤ (horizontalLaneBase piece.role : ℝ)+(drawingGridSize graph : ℝ)*
          (coreCell.2+horizontalLaneCellShift tagged.1 piece.role : Int) := by
      push_cast
      constructor <;> nlinarith [fixed]
    have above : (2 : Int) < horizontalLaneBase piece.role := by
      rcases classifiedCore_horizontal_low_or_high graph tagged.1 tagged.2 piece pieceMember role with low | high
      · rw [low]
        simp only [horizontalLaneBase,edgeTrack]
        omega
      · rw [high]
        simp only [horizontalLaneBase,edgeTrack]
        omega
    exact GridSegment.normalized_bands_disjoint (point := point.2) gridPositive
      (by omega : (0 : Int) ≤ 2 ∧ (2 : Int) < drawingGridSize graph)
      (classifiedCore_horizontal_lane_bounds member pieceMember role) (Or.inl above) vertexYBand band
  · have column := classifiedCore_vertical_column graph tagged.1 tagged.2 edgeLocal piece pieceMember vertical
    have avoidColumn (base shift : Int) (normalized : 0 ≤ base ∧ base < drawingGridSize graph)
        (outside : (position graph index).1 < base ∨ base < (position graph index).1)
        (stored : piece.segment.start.1 = base+(drawingGridSize graph : Int)*shift) : False := by
      have fixed := GridSegment.realContains_vertical_x ((GridSegment.isVertical_translate _ _).mpr vertical) contains
      change point.1 = (((drawingGridSize graph : Int)*coreCell.1+piece.segment.start.1 : Int) : ℝ) at fixed
      rw [stored] at fixed
      push_cast at fixed
      have band : (base : ℝ)+(drawingGridSize graph : ℝ)*(coreCell.1+shift : Int) ≤ point.1 ∧
          point.1 ≤ (base : ℝ)+(drawingGridSize graph : ℝ)*(coreCell.1+shift : Int) := by
        push_cast
        constructor <;> nlinarith [fixed]
      exact GridSegment.normalized_bands_disjoint (point := point.1) gridPositive
        (by omega : 0 ≤ (position graph index).1 ∧ (position graph index).1 < drawingGridSize graph)
        normalized outside vertexXBand band
    have kind := classifiedCore_vertical_role graph tagged.1 tagged.2 piece pieceMember vertical
    rcases kind with active | boundary
    · have portOrGate : (∃ port, piece.role.activeVerticalPort = some port) ∨ ∃ gateIndex, piece.role = .gateVertical gateIndex := by
        cases roleEq : piece.role <;> simp_all [SegmentRole.IsActiveVertical,SegmentRole.activeVerticalPort]
      rcases portOrGate with ⟨port,spine⟩ | ⟨gateIndex,gateRole⟩
      · have band := core_port_spine_band graph tagged.1 tagged.2 edgeLocal piece pieceMember port spine
        have box := GridSegment.realBoxContains_of_realContains contains
        simp only [GridSegment.RealBoxContains,GridSegment.translate,Cell.scale,Cell.add,min_add_add_left,
          max_add_add_left,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_min,Int.cast_max] at box
        have lo : (3 : ℝ)+(drawingGridSize graph : ℝ)*(corePortShift tagged.1 piece.role).2 ≤
            (min piece.segment.start.2 piece.segment.finish.2 : Int) := by exact_mod_cast band.2.1
        have hi : (max piece.segment.start.2 piece.segment.finish.2 : Int) ≤
            (edgeTrack tagged.2+1 : Int)+(drawingGridSize graph : ℝ)*(corePortShift tagged.1 piece.role).2 := by exact_mod_cast band.2.2
        push_cast at lo hi
        have realBand : ((3 : Int) : ℝ)+(drawingGridSize graph : ℝ)*
              (coreCell.2+(corePortShift tagged.1 piece.role).2 : Int) ≤ point.2 ∧
            point.2 ≤ (edgeTrack tagged.2+1 : Int)+(drawingGridSize graph : ℝ)*
              (coreCell.2+(corePortShift tagged.1 piece.role).2 : Int) := by
          push_cast
          norm_num only [Int.cast_ofNat]
          exact ⟨by nlinarith [box.2.2.1,lo],by nlinarith [box.2.2.2,hi]⟩
        have tracks := edgeTrack_bounds graph member
        exact GridSegment.normalized_bands_disjoint (point := point.2) gridPositive
          (by omega : (0 : Int) ≤ 2 ∧ (2 : Int) < drawingGridSize graph)
          (by omega : (0 : Int) ≤ 3 ∧ edgeTrack tagged.2+1 < drawingGridSize graph)
          (Or.inl (by omega : (2 : Int) < 3)) vertexYBand realBand
      · have indexEq := classifiedCore_role_index graph tagged.1 tagged.2 piece pieceMember
        rw [gateRole] at indexEq
        change gateIndex = tagged.2 at indexEq
        subst gateIndex
        simp only [gateRole,verticalBase,verticalShift,mul_zero,add_zero] at column
        have edgeValid : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
        apply avoidColumn (gateX graph tagged.2) 0
        · unfold gateX drawingGridSize
          omega
        · exact Or.inl (vertexBounds.2.2 tagged.2)
        · simpa using column
    · simp only [boundary,verticalBase,verticalShift,zero_add] at column
      exact avoidColumn 0 (max tagged.1.offset.1 0)
        (by omega : (0 : Int) ≤ 0 ∧ (0 : Int) < drawingGridSize graph)
        (Or.inr (by omega : (0 : Int) < (position graph index).1)) (by simpa using column)

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

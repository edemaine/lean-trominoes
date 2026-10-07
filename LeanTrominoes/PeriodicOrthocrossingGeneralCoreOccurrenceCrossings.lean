/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreProperCrossings
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreJoints

/-! # Core contacts are proper crossings even between copies of the same protoedge -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem horizontal_core_avoids_port_row {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {tagged : PeriodicEdge Vertex × Nat}
    (edgeMember : tagged ∈ graph.edges.zipIdx) {piece : ClassifiedSegment Vertex}
    (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2) (horizontal : piece.segment.IsHorizontal)
    {endpoint : Cell} (portRow : PortRow graph endpoint.2) (firstCell secondCell : Cell) :
    ¬(piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint)) := by
  intro contains
  have role := classifiedCore_horizontal_role graph tagged.1 tagged.2 piece pieceMember horizontal
  have fixed := GridSegment.realContains_horizontal_y ((GridSegment.isHorizontal_translate _ _).mpr horizontal) contains
  change ((Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).2 : ℝ) =
    ((piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.2 : ℝ) at fixed
  have fixedInt : (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).2 =
      (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.2 := by exact_mod_cast fixed
  change (drawingGridSize graph : Int)*secondCell.2+endpoint.2 =
    (drawingGridSize graph : Int)*firstCell.2+piece.segment.start.2 at fixedInt
  rw [classifiedCore_horizontal_lane graph tagged.1 tagged.2 piece pieceMember role] at fixedInt
  obtain ⟨shift,row⟩ := portRow
  rw [row] at fixedInt
  have normalized : horizontalLaneBase piece.role+(drawingGridSize graph : Int)*
        (horizontalLaneCellShift tagged.1 piece.role+firstCell.2) =
      3+(drawingGridSize graph : Int)*(shift+secondCell.2) := by linear_combination -fixedInt
  have gridThree : (3 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  have lanes := periodic_coordinate_unique (by exact_mod_cast drawingGridSize_pos graph)
    (classifiedCore_horizontal_lane_bounds edgeMember pieceMember role)
    (by omega : (0 : Int) ≤ 3 ∧ (3 : Int) < drawingGridSize graph) normalized
  rcases classifiedCore_horizontal_low_or_high graph tagged.1 tagged.2 piece pieceMember role with low | high
  · rw [low] at lanes
    simp only [horizontalLaneBase,edgeTrack] at lanes
    omega
  · rw [high] at lanes
    simp only [horizontalLaneBase,edgeTrack] at lanes
    omega

theorem perpendicular_core_occurrence_contact_is_proper {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {horizontalTagged verticalTagged : PeriodicEdge Vertex × Nat}
    (horizontalEdgeMember : horizontalTagged ∈ graph.edges.zipIdx) (verticalEdgeMember : verticalTagged ∈ graph.edges.zipIdx)
    (horizontalLocal : horizontalTagged.1.span ≤ 1) (verticalLocal : verticalTagged.1.span ≤ 1)
    {horizontalPiece verticalPiece : ClassifiedSegment Vertex}
    (horizontalMember : horizontalPiece ∈ classifiedCore graph horizontalTagged.1 horizontalTagged.2)
    (verticalMember : verticalPiece ∈ classifiedCore graph verticalTagged.1 verticalTagged.2)
    (horizontal : horizontalPiece.segment.IsHorizontal) (vertical : verticalPiece.segment.IsVertical)
    {firstCell secondCell : Cell} (different : (horizontalTagged,firstCell) ≠ (verticalTagged,secondCell)) {point : ℝ × ℝ}
    (firstContains : (horizontalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (verticalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    PeriodicGridDrawing.RealProperlyCrossesAt
      (horizontalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell))
      (verticalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)) point := by
  have horizontalJoints := core_horizontal_endpoint_joints wellFormed horizontalEdgeMember horizontalLocal
    horizontalPiece horizontalMember horizontal
  have verticalJoints := core_vertical_endpoint_joints wellFormed verticalEdgeMember verticalLocal
    verticalPiece verticalMember vertical
  have horizontalClear (endpoint : Cell) (joint : CoreJoint graph horizontalTagged.1 horizontalTagged.2 false endpoint) :
      point ≠ realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) firstCell) endpoint) := by
    intro atEndpoint
    obtain ⟨neighbor,member,axis,contains⟩ := coreJoint_translated_contains joint firstCell
    rw [← atEndpoint] at contains
    have unique := vertical_core_contacts_unique wellFormed horizontalEdgeMember verticalEdgeMember horizontalLocal verticalLocal
      member verticalMember axis vertical contains secondContains
    exact different (Prod.ext unique.1 unique.2.2)
  have verticalClear (endpoint : Cell)
      (joint : CoreJoint graph verticalTagged.1 verticalTagged.2 true endpoint ∨ PortRow graph endpoint.2) :
      point ≠ realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint) := by
    intro atEndpoint
    rcases joint with joint | portRow
    · obtain ⟨neighbor,member,axis,contains⟩ := coreJoint_translated_contains joint secondCell
      rw [← atEndpoint] at contains
      have unique := horizontal_core_contacts_unique wellFormed horizontalEdgeMember verticalEdgeMember horizontalLocal
        horizontalMember member horizontal axis firstContains contains
      exact different (Prod.ext unique.1 unique.2.2)
    · rw [atEndpoint] at firstContains
      exact horizontal_core_avoids_port_row horizontalEdgeMember horizontalMember horizontal portRow firstCell secondCell firstContains
  exact ⟨GridSegment.realInteriorContains_of_realContains_of_not_endpoints firstContains
      (horizontalClear _ horizontalJoints.1) (horizontalClear _ horizontalJoints.2),
    GridSegment.realInteriorContains_of_realContains_of_not_endpoints secondContains
      (verticalClear _ verticalJoints.1) (verticalClear _ verticalJoints.2),
    Or.inl ⟨(GridSegment.isHorizontal_translate _ _).mpr horizontal,(GridSegment.isVertical_translate _ _).mpr vertical⟩⟩

theorem core_contacts_distinct_occurrences_are_proper {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstEdgeMember : firstTagged ∈ graph.edges.zipIdx) (secondEdgeMember : secondTagged ∈ graph.edges.zipIdx)
    (firstLocal : firstTagged.1.span ≤ 1) (secondLocal : secondTagged.1.span ≤ 1)
    {firstPiece secondPiece : ClassifiedSegment Vertex}
    (firstMember : firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2)
    (secondMember : secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    {firstCell secondCell : Cell} (different : (firstTagged,firstCell) ≠ (secondTagged,secondCell)) {point : ℝ × ℝ}
    (firstContains : (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    PeriodicGridDrawing.RealProperlyCrossesAt
      (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell))
      (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)) point := by
  have firstAxis : firstPiece.segment.IsAxisAligned := by
    apply (orthogonalPolyline_iff_segments _).mp (core_orthogonal wellFormed firstEdgeMember firstLocal)
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨firstPiece,firstMember,rfl⟩
  have secondAxis : secondPiece.segment.IsAxisAligned := by
    apply (orthogonalPolyline_iff_segments _).mp (core_orthogonal wellFormed secondEdgeMember secondLocal)
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨secondPiece,secondMember,rfl⟩
  rcases firstAxis with firstHorizontal | firstVertical <;> rcases secondAxis with secondHorizontal | secondVertical
  · have unique := horizontal_core_contacts_unique wellFormed firstEdgeMember secondEdgeMember firstLocal
      firstMember secondMember firstHorizontal secondHorizontal firstContains secondContains
    exact (different (Prod.ext unique.1 unique.2.2)).elim
  · exact perpendicular_core_occurrence_contact_is_proper wellFormed firstEdgeMember secondEdgeMember firstLocal secondLocal
      firstMember secondMember firstHorizontal secondVertical different firstContains secondContains
  · have cross := perpendicular_core_occurrence_contact_is_proper wellFormed secondEdgeMember firstEdgeMember secondLocal firstLocal
      secondMember firstMember secondHorizontal firstVertical different.symm secondContains firstContains
    exact ⟨cross.2.1,cross.1,Or.inr ⟨(GridSegment.isVertical_translate _ _).mpr firstVertical,
      (GridSegment.isHorizontal_translate _ _).mpr secondHorizontal⟩⟩
  · have unique := vertical_core_contacts_unique wellFormed firstEdgeMember secondEdgeMember firstLocal secondLocal
      firstMember secondMember firstVertical secondVertical firstContains secondContains
    exact (different (Prod.ext unique.1 unique.2.2)).elim

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralPrivateRowContact
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralPrivateColumnContact
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralBoundaryContact
import LeanTrominoes.Common.Geometry.GridSegmentRealInterior

/-! # Distinct protoedges meet in their cores only at proper orthogonal crossings -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem perpendicular_core_contact_is_proper {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {horizontalTagged verticalTagged : PeriodicEdge Vertex × Nat}
    (horizontalEdgeMember : horizontalTagged ∈ graph.edges.zipIdx) (verticalEdgeMember : verticalTagged ∈ graph.edges.zipIdx)
    (horizontalLocal : horizontalTagged.1.span ≤ 1) (verticalLocal : verticalTagged.1.span ≤ 1)
    (different : horizontalTagged.2 ≠ verticalTagged.2)
    {horizontalPiece verticalPiece : ClassifiedSegment Vertex}
    (horizontalMember : horizontalPiece ∈ classifiedCore graph horizontalTagged.1 horizontalTagged.2)
    (verticalMember : verticalPiece ∈ classifiedCore graph verticalTagged.1 verticalTagged.2)
    (horizontal : horizontalPiece.segment.IsHorizontal) (vertical : verticalPiece.segment.IsVertical)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (horizontalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (verticalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    PeriodicGridDrawing.RealProperlyCrossesAt
      (horizontalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell))
      (verticalPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)) point := by
  have kind := classifiedCore_vertical_role graph verticalTagged.1 verticalTagged.2 verticalPiece verticalMember vertical
  have active : verticalPiece.role.IsActiveVertical := by
    rcases kind with active | boundary
    · exact active
    · exact (different (horizontal_boundary_contacts_index horizontalEdgeMember verticalEdgeMember
        horizontalMember verticalMember horizontal boundary firstContains secondContains)).elim
  have columns := classifiedCore_endpoint_columns graph horizontalTagged.1 horizontalTagged.2 horizontalLocal horizontalMember
  have rows := classifiedCore_endpoint_rows graph verticalTagged.1 verticalTagged.2 verticalLocal verticalMember
  refine ⟨?_,?_,Or.inl ⟨(GridSegment.isHorizontal_translate _ _).mpr horizontal,
    (GridSegment.isVertical_translate _ _).mpr vertical⟩⟩
  · apply GridSegment.realInteriorContains_of_realContains_of_not_endpoints firstContains
    · intro endpoint
      rw [endpoint] at secondContains
      exact different (vertical_endpoint_contact_index wellFormed verticalEdgeMember horizontalEdgeMember verticalLocal
        verticalMember active vertical columns.1 secondCell firstCell secondContains).symm
    · intro endpoint
      rw [endpoint] at secondContains
      exact different (vertical_endpoint_contact_index wellFormed verticalEdgeMember horizontalEdgeMember verticalLocal
        verticalMember active vertical columns.2 secondCell firstCell secondContains).symm
  · apply GridSegment.realInteriorContains_of_realContains_of_not_endpoints secondContains
    · intro endpoint
      rw [endpoint] at firstContains
      exact different (horizontal_endpoint_contact_index horizontalEdgeMember verticalEdgeMember
        horizontalMember horizontal rows.1 firstCell secondCell firstContains)
    · intro endpoint
      rw [endpoint] at firstContains
      exact different (horizontal_endpoint_contact_index horizontalEdgeMember verticalEdgeMember
        horizontalMember horizontal rows.2 firstCell secondCell firstContains)

theorem core_contacts_distinct_edges_are_proper {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstEdgeMember : firstTagged ∈ graph.edges.zipIdx) (secondEdgeMember : secondTagged ∈ graph.edges.zipIdx)
    (firstLocal : firstTagged.1.span ≤ 1) (secondLocal : secondTagged.1.span ≤ 1)
    (different : firstTagged.2 ≠ secondTagged.2)
    {firstPiece secondPiece : ClassifiedSegment Vertex}
    (firstMember : firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2)
    (secondMember : secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
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
    exact (different (congrArg Prod.snd unique.1)).elim
  · exact perpendicular_core_contact_is_proper wellFormed firstEdgeMember secondEdgeMember firstLocal secondLocal
      different firstMember secondMember firstHorizontal secondVertical firstContains secondContains
  · have cross := perpendicular_core_contact_is_proper wellFormed secondEdgeMember firstEdgeMember secondLocal firstLocal
      different.symm secondMember firstMember secondHorizontal firstVertical secondContains firstContains
    exact ⟨cross.2.1,cross.1,Or.inr ⟨(GridSegment.isVertical_translate _ _).mpr firstVertical,
      (GridSegment.isHorizontal_translate _ _).mpr secondHorizontal⟩⟩
  · have unique := vertical_core_contacts_unique wellFormed firstEdgeMember secondEdgeMember firstLocal secondLocal
      firstMember secondMember firstVertical secondVertical firstContains secondContains
    exact (different (congrArg Prod.snd unique.1)).elim

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

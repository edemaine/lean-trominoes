/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreVertical
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreSpans
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisCoordinates

/-! # Distinct vertical core occurrences have disjoint closed images -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem boundary_core_contacts_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstEdgeMember : firstTagged ∈ graph.edges.zipIdx) (secondEdgeMember : secondTagged ∈ graph.edges.zipIdx)
    {firstPiece secondPiece : ClassifiedSegment Vertex}
    (firstMember : firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2)
    (secondMember : secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    (firstBoundary : firstPiece.role = .boundaryVertical firstTagged.2)
    (secondBoundary : secondPiece.role = .boundaryVertical secondTagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged.2 = secondTagged.2 := by
  have firstEnds := classifiedCore_boundary_bounds graph firstTagged.1 firstTagged.2 firstPiece firstMember firstBoundary
  have secondEnds := classifiedCore_boundary_bounds graph secondTagged.1 secondTagged.2 secondPiece secondMember secondBoundary
  have firstBox := GridSegment.realBoxContains_of_realContains firstContains
  have secondBox := GridSegment.realBoxContains_of_realContains secondContains
  simp only [GridSegment.RealBoxContains,GridSegment.translate,Cell.scale,Cell.add,
    min_add_add_left,max_add_add_left,Int.cast_add,Int.cast_mul] at firstBox secondBox
  rw [firstEnds.1,firstEnds.2,
    min_eq_left (by omega : edgeTrack firstTagged.2 ≤ edgeTrack firstTagged.2+1),
    max_eq_right (by omega : edgeTrack firstTagged.2 ≤ edgeTrack firstTagged.2+1)] at firstBox
  rw [secondEnds.1,secondEnds.2,
    min_eq_left (by omega : edgeTrack secondTagged.2 ≤ edgeTrack secondTagged.2+1),
    max_eq_right (by omega : edgeTrack secondTagged.2 ≤ edgeTrack secondTagged.2+1)] at secondBox
  simp only [Int.cast_natCast,Int.cast_add,Int.cast_one] at firstBox secondBox
  have firstTracks := edgeTrack_bounds graph firstEdgeMember
  have secondTracks := edgeTrack_bounds graph secondEdgeMember
  have firstBounds : (edgeTrack firstTagged.2 : ℝ)+(drawingGridSize graph : ℝ)*firstCell.2 ≤ point.2 ∧
      point.2 ≤ (edgeTrack firstTagged.2+1 : Int)+(drawingGridSize graph : ℝ)*firstCell.2 :=
    ⟨by linarith [firstBox.2.2.1],by push_cast; linarith [firstBox.2.2.2]⟩
  have secondBounds : (edgeTrack secondTagged.2 : ℝ)+(drawingGridSize graph : ℝ)*secondCell.2 ≤ point.2 ∧
      point.2 ≤ (edgeTrack secondTagged.2+1 : Int)+(drawingGridSize graph : ℝ)*secondCell.2 :=
    ⟨by linarith [secondBox.2.2.1],by push_cast; linarith [secondBox.2.2.2]⟩
  have shifts := GridSegment.normalized_bands_periodic_shifts_unique
    (point := point.2) (by exact_mod_cast drawingGridSize_pos graph)
    (by omega : 0 ≤ edgeTrack firstTagged.2 ∧ edgeTrack firstTagged.2+1 < drawingGridSize graph)
    (by omega : 0 ≤ edgeTrack secondTagged.2 ∧ edgeTrack secondTagged.2+1 < drawingGridSize graph)
    firstBounds secondBounds
  rw [shifts] at firstBounds
  have firstLe : edgeTrack firstTagged.2 ≤ edgeTrack secondTagged.2+1 := by
    exact_mod_cast (by linarith [firstBounds.1,secondBounds.2] :
      (edgeTrack firstTagged.2 : ℝ) ≤ (edgeTrack secondTagged.2+1 : Int))
  have secondLe : edgeTrack secondTagged.2 ≤ edgeTrack firstTagged.2+1 := by
    exact_mod_cast (by linarith [secondBounds.1,firstBounds.2] :
      (edgeTrack secondTagged.2 : ℝ) ≤ (edgeTrack firstTagged.2+1 : Int))
  unfold edgeTrack at firstLe secondLe
  omega

theorem vertical_core_contacts_unique {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstEdgeMember : firstTagged ∈ graph.edges.zipIdx) (secondEdgeMember : secondTagged ∈ graph.edges.zipIdx)
    (firstLocal : firstTagged.1.span ≤ 1) (secondLocal : secondTagged.1.span ≤ 1)
    {firstPiece secondPiece : ClassifiedSegment Vertex}
    (firstMember : firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2)
    (secondMember : secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    (firstVertical : firstPiece.segment.IsVertical) (secondVertical : secondPiece.segment.IsVertical)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged = secondTagged ∧ firstPiece = secondPiece ∧ firstCell = secondCell := by
  have firstFixed := GridSegment.realContains_vertical_x
    ((GridSegment.isVertical_translate _ _).mpr firstVertical) firstContains
  have secondFixed := GridSegment.realContains_vertical_x
    ((GridSegment.isVertical_translate _ _).mpr secondVertical) secondContains
  have scalarEqual :
      (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.1 =
      (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).start.1 := by
    exact_mod_cast firstFixed.symm.trans secondFixed
  change (drawingGridSize graph : Int)*firstCell.1+firstPiece.segment.start.1 =
    (drawingGridSize graph : Int)*secondCell.1+secondPiece.segment.start.1 at scalarEqual
  rw [classifiedCore_vertical_column graph firstTagged.1 firstTagged.2 firstLocal firstPiece firstMember firstVertical,
    classifiedCore_vertical_column graph secondTagged.1 secondTagged.2 secondLocal secondPiece secondMember secondVertical] at scalarEqual
  have normalizedEqual : verticalBase graph firstPiece.role+(drawingGridSize graph : Int)*
          (verticalShift firstTagged.1 firstPiece.role+firstCell.1) =
      verticalBase graph secondPiece.role+(drawingGridSize graph : Int)*
          (verticalShift secondTagged.1 secondPiece.role+secondCell.1) := by linear_combination scalarEqual
  have lanes := periodic_coordinate_unique (by exact_mod_cast drawingGridSize_pos graph)
    (classifiedCore_vertical_base_bounds wellFormed firstEdgeMember firstPiece firstMember firstVertical)
    (classifiedCore_vertical_base_bounds wellFormed secondEdgeMember secondPiece secondMember secondVertical) normalizedEqual
  have firstKind := classifiedCore_vertical_role graph firstTagged.1 firstTagged.2 firstPiece firstMember firstVertical
  have secondKind := classifiedCore_vertical_role graph secondTagged.1 secondTagged.2 secondPiece secondMember secondVertical
  have rolesEqual : firstPiece.role = secondPiece.role := by
    rcases firstKind with firstActive | firstBoundary <;> rcases secondKind with secondActive | secondBoundary
    · exact active_vertical_roles_eq_of_bases_eq wellFormed firstActive secondActive
        (classifiedCore_activeEnd_correct graph firstTagged.1 firstTagged.2 firstPiece firstMember)
        (classifiedCore_activeEnd_correct graph secondTagged.1 secondTagged.2 secondPiece secondMember)
        (classifiedCore_activePort_mem firstEdgeMember firstPiece firstMember)
        (classifiedCore_activePort_mem secondEdgeMember secondPiece secondMember) lanes.1
    · have positive := classifiedCore_active_base_positive wellFormed firstEdgeMember firstMember firstActive
      have zero : verticalBase graph secondPiece.role = 0 := by rw [secondBoundary]; rfl
      omega
    · have positive := classifiedCore_active_base_positive wellFormed secondEdgeMember secondMember secondActive
      have zero : verticalBase graph firstPiece.role = 0 := by rw [firstBoundary]; rfl
      omega
    · have indices := boundary_core_contacts_index firstEdgeMember secondEdgeMember firstMember secondMember
        firstBoundary secondBoundary firstContains secondContains
      rw [firstBoundary,secondBoundary,indices]
  have indicesEqual := congrArg SegmentRole.edgeIndex rolesEqual
  rw [classifiedCore_role_index graph firstTagged.1 firstTagged.2 firstPiece firstMember,
    classifiedCore_role_index graph secondTagged.1 secondTagged.2 secondPiece secondMember] at indicesEqual
  have edgesEqual := tagged_eq_of_mem_zipIdx_of_snd_eq firstEdgeMember secondEdgeMember indicesEqual
  cases edgesEqual
  have piecesEqual := classifiedCore_role_unique graph firstTagged.1 firstTagged.2
    firstPiece firstMember secondPiece secondMember rolesEqual
  refine ⟨rfl,piecesEqual,?_⟩
  rw [← piecesEqual] at secondContains
  exact core_piece_copies_disjoint wellFormed firstEdgeMember firstLocal firstMember firstContains secondContains

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreHorizontal
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreSpans
import LeanTrominoes.GridSegmentRealAxisCoordinates

/-! # Distinct horizontal core occurrences have disjoint closed images -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem horizontal_core_contacts_unique {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstEdgeMember : firstTagged ∈ graph.edges.zipIdx) (secondEdgeMember : secondTagged ∈ graph.edges.zipIdx)
    (firstLocal : firstTagged.1.span ≤ 1)
    {firstPiece secondPiece : ClassifiedSegment Vertex}
    (firstMember : firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2)
    (secondMember : secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    (firstHorizontal : firstPiece.segment.IsHorizontal) (secondHorizontal : secondPiece.segment.IsHorizontal)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged = secondTagged ∧ firstPiece = secondPiece ∧ firstCell = secondCell := by
  have firstRole := classifiedCore_horizontal_role graph firstTagged.1 firstTagged.2
    firstPiece firstMember firstHorizontal
  have secondRole := classifiedCore_horizontal_role graph secondTagged.1 secondTagged.2
    secondPiece secondMember secondHorizontal
  have firstFixed := GridSegment.realContains_horizontal_y
    ((GridSegment.isHorizontal_translate _ _).mpr firstHorizontal) firstContains
  have secondFixed := GridSegment.realContains_horizontal_y
    ((GridSegment.isHorizontal_translate _ _).mpr secondHorizontal) secondContains
  have scalarEqual :
      (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.2 =
      (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).start.2 := by
    exact_mod_cast firstFixed.symm.trans secondFixed
  change (drawingGridSize graph : Int)*firstCell.2+firstPiece.segment.start.2 =
    (drawingGridSize graph : Int)*secondCell.2+secondPiece.segment.start.2 at scalarEqual
  rw [classifiedCore_horizontal_lane graph firstTagged.1 firstTagged.2 firstPiece firstMember firstRole,
    classifiedCore_horizontal_lane graph secondTagged.1 secondTagged.2 secondPiece secondMember secondRole] at scalarEqual
  have normalizedEqual :
      horizontalLaneBase firstPiece.role+(drawingGridSize graph : Int)*
          (horizontalLaneCellShift firstTagged.1 firstPiece.role+firstCell.2) =
      horizontalLaneBase secondPiece.role+(drawingGridSize graph : Int)*
          (horizontalLaneCellShift secondTagged.1 secondPiece.role+secondCell.2) := by
    linear_combination scalarEqual
  have lanes := periodic_coordinate_unique (by exact_mod_cast drawingGridSize_pos graph)
    (classifiedCore_horizontal_lane_bounds firstEdgeMember firstMember firstRole)
    (classifiedCore_horizontal_lane_bounds secondEdgeMember secondMember secondRole) normalizedEqual
  have rolesEqual : firstPiece.role = secondPiece.role := by
    rcases horizontal_roles_eq_or_both_fanout firstRole secondRole lanes.1 with equal | bothFanout
    · exact equal
    · rcases classifiedCore_horizontal_low_or_high graph firstTagged.1 firstTagged.2
        firstPiece firstMember firstRole with low | high
      · rw [low] at bothFanout
        simp [SegmentRole.IsHorizontalFanout] at bothFanout
      · rw [high] at bothFanout
        simp [SegmentRole.IsHorizontalFanout] at bothFanout
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

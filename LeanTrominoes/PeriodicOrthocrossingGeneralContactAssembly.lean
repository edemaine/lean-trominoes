/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralLiftedRouteParts
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreOccurrenceCrossings

/-! # Complete route occurrences meet only at endpoints or proper core crossings -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core route classifiedCore

theorem route_fan_core_contacts_same_occurrence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (secondLocal : secondTagged.1.span ≤ 1) {piece : ClassifiedSegment Vertex}
    (pieceMember : piece ∈ classifiedCore graph secondTagged.1 secondTagged.2) (target : Bool)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (routeFanCell firstTagged firstCell target))
        (fan graph orthogonal (routeFanPort firstTagged target))) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged = secondTagged ∧ firstCell = secondCell := by
  cases target
  · exact source_fan_core_contacts_same_occurrence wellFormed orthogonal degree firstMember secondMember
      secondLocal pieceMember fanContains coreContains
  · exact target_fan_core_contacts_same_occurrence wellFormed orthogonal degree firstMember secondMember
      secondLocal pieceMember fanContains coreContains

theorem route_occurrence_contacts {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (firstLocal : firstTagged.1.span ≤ 1) (secondLocal : secondTagged.1.span ≤ 1)
    {firstCell secondCell : Cell} (different : (firstTagged,firstCell) ≠ (secondTagged,secondCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell)
      (route graph orthogonal firstTagged.1 firstTagged.2)) point)
    (secondContains : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell)
      (route graph orthogonal secondTagged.1 secondTagged.2)) point) :
    (GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell)
        (route graph orthogonal firstTagged.1 firstTagged.2)) point ∧
      GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell)
        (route graph orthogonal secondTagged.1 secondTagged.2)) point) ∨
      ∃ firstPiece ∈ classifiedCore graph firstTagged.1 firstTagged.2,
        ∃ secondPiece ∈ classifiedCore graph secondTagged.1 secondTagged.2,
          PeriodicGridDrawing.RealProperlyCrossesAt
            (firstPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell))
            (secondPiece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)) point := by
  have firstPart := lifted_route_realContains_parts orthogonal degree firstMember firstContains
  have secondPart := lifted_route_realContains_parts orthogonal degree secondMember secondContains
  rcases firstPart with ⟨firstTarget,firstFan⟩ | ⟨firstPiece,firstPieceMember,firstCore⟩
  · rcases secondPart with ⟨secondTarget,secondFan⟩ | ⟨secondPiece,secondPieceMember,secondCore⟩
    · exact Or.inl (route_fans_meet_only_at_endpoints wellFormed orthogonal degree firstMember secondMember
        firstTarget secondTarget different firstFan secondFan)
    · have same := route_fan_core_contacts_same_occurrence wellFormed orthogonal degree firstMember secondMember
        secondLocal secondPieceMember firstTarget firstFan secondCore
      exact (different (Prod.ext same.1 same.2)).elim
  · rcases secondPart with ⟨secondTarget,secondFan⟩ | ⟨secondPiece,secondPieceMember,secondCore⟩
    · have same := route_fan_core_contacts_same_occurrence wellFormed orthogonal degree secondMember firstMember
        firstLocal firstPieceMember secondTarget secondFan firstCore
      exact (different (Prod.ext same.1 same.2).symm).elim
    · exact Or.inr ⟨firstPiece,firstPieceMember,secondPiece,secondPieceMember,
        core_contacts_distinct_occurrences_are_proper wellFormed firstMember secondMember firstLocal secondLocal
          firstPieceMember secondPieceMember different firstCore secondCore⟩

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

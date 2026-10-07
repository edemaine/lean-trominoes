/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteComponents

/-! # A complete route's fan cannot meet the core of a different route occurrence -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core classifiedCore route

theorem source_fan_core_contacts_same_occurrence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (secondLocal : secondTagged.1.span ≤ 1) {piece : ClassifiedSegment Vertex}
    (pieceMember : piece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell)
      (fan graph orthogonal (sourcePort firstTagged.1 firstTagged.2))) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged = secondTagged ∧ firstCell = secondCell := by
  have contact := fan_core_contacts_only_at_joint wellFormed orthogonal degree
    (sourcePort_mem_allPorts graph firstMember) secondMember secondLocal pieceMember fanContains coreContains
  rcases contact.2 with ⟨ports,cells⟩ | ⟨ports,_⟩
  · have indices := congrArg GraphPort.edgeIndex ports
    change firstTagged.2 = secondTagged.2 at indices
    exact ⟨tagged_eq_of_mem_zipIdx_of_snd_eq firstMember secondMember indices,cells⟩
  · have kinds := congrArg GraphPort.endKind ports
    cases kinds

theorem target_fan_core_contacts_same_occurrence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (secondLocal : secondTagged.1.span ≤ 1) {piece : ClassifiedSegment Vertex}
    (pieceMember : piece ∈ classifiedCore graph secondTagged.1 secondTagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (Cell.add firstCell firstTagged.1.offset))
        (fan graph orthogonal (targetPort firstTagged.1 firstTagged.2))) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstTagged = secondTagged ∧ firstCell = secondCell := by
  have contact := fan_core_contacts_only_at_joint wellFormed orthogonal degree
    (targetPort_mem_allPorts graph firstMember) secondMember secondLocal pieceMember fanContains coreContains
  rcases contact.2 with ⟨ports,_⟩ | ⟨ports,cells⟩
  · have kinds := congrArg GraphPort.endKind ports
    cases kinds
  · have indices := congrArg GraphPort.edgeIndex ports
    change firstTagged.2 = secondTagged.2 at indices
    have taggedEq := tagged_eq_of_mem_zipIdx_of_snd_eq firstMember secondMember indices
    refine ⟨taggedEq,?_⟩
    rw [← taggedEq] at cells
    apply Prod.ext
    · have x := congrArg Prod.fst cells
      simp only [Cell.add] at x
      omega
    · have y := congrArg Prod.snd cells
      simp only [Cell.add] at y
      omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContraction
import LeanTrominoes.PeriodicThreeDMOneDimensional

/-!
# Horizontal contraction of one-dimensional periodic 3DM

Every incidence offset of a one-dimensional periodic 3DM instance is
horizontal.  Consequently suppressing degree-two colored vertices creates
only horizontal contracted-edge offsets.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Every genuine incidence of a one-dimensional instance has zero vertical
offset. -/
theorem incidence_offset_vertical_eq_zero
    {problem : PeriodicThreeDM}
    (horizontal : problem.IsOneDimensional)
    (color : WireColor) (atom : Nat) {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    incidence.offset.2 = 0 := by
  simp only [incidences, List.mem_filterMap] at member
  rcases member with ⟨tripleIndex, tripleIndexMember, produced⟩
  have tripleIndexLt : tripleIndex < problem.triples.length :=
    List.mem_range.mp tripleIndexMember
  split at produced
  next same =>
    injection produced with incidenceEq
    subst incidence
    have tripleMember :
        problem.triples.getD tripleIndex default ∈ problem.triples := by
      rw [List.getD_eq_getElem _ _ tripleIndexLt]
      exact List.getElem_mem _
    exact horizontal
      (problem.triples.getD tripleIndex default) tripleMember color
  next different =>
    simp at produced

/-- Every edge emitted by contraction of a one-dimensional instance has zero
vertical period offset. -/
theorem contractedEdge_offset_vertical_eq_zero
    {problem : PeriodicThreeDM}
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.toPeriodicEdge.offset.2 = 0 := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, _colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, _atomMember, member⟩
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom member
  have sourceHorizontal :=
    incidence_offset_vertical_eq_zero horizontal color atom
      incidenceMembers.1
  have targetHorizontal :=
    incidence_offset_vertical_eq_zero horizontal color atom
      incidenceMembers.2.1
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simpa [ContractedEdge.sourceIncidence,
        ContractedEdge.toPeriodicEdge] using sourceHorizontal
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.sourceIncidence] at sourceHorizontal
      simp only [ContractedEdge.targetIncidence] at targetHorizontal
      simp [ContractedEdge.toPeriodicEdge, Cell.sub,
        sourceHorizontal, targetHorizontal]

end PeriodicThreeDM
end LeanTrominoes

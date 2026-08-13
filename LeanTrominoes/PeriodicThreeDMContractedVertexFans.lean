/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractedEndpointDirectionSeparation

/-!
# Colored normalization fans at contracted 3DM vertices

Every retained vertex has three endpoint occurrences.  This module packages
those occurrences as the `ColoredFan` consumed by the finite degree-three
normalization templates.  Triple vertices have three distinct RGB colors;
retained element vertices are monochromatic.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Distinct endpoints at one vertex also determine distinct template
sides. -/
theorem ContractedEndpoint.outwardSide_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.outwardSide presentation.toPlanarPresentation ≠
      second.outwardSide presentation.toPlanarPresentation := by
  intro sidesEqual
  apply first.outwardDirection_ne presentation degree
    firstMember secondMember different sameVertex
  rw [← first.outwardSide_direction presentation.toPlanarPresentation
      degree firstMember,
    ← second.outwardSide_direction presentation.toPlanarPresentation
      degree secondMember,
    sidesEqual]

/-- A triple of endpoint occurrences, in executable enumeration order,
equipped with the geometric side-separation certificate. -/
structure ContractedVertexFan
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (vertex : PeriodicThreeDMVertex) where
  first : ContractedEndpoint
  second : ContractedEndpoint
  third : ContractedEndpoint
  endpoints_eq :
    problem.contractedEndpointsAt vertex = [first, second, third]
  sidesNodup :
    [first.outwardSide presentation.toPlanarPresentation,
      second.outwardSide presentation.toPlanarPresentation,
      third.outwardSide presentation.toPlanarPresentation].Nodup

namespace ContractedVertexFan

/-- Forget endpoint identities while retaining exactly the local template
data. -/
def coloredFan
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) : ColoredFan where
  firstSide := fan.first.outwardSide presentation.toPlanarPresentation
  secondSide := fan.second.outwardSide presentation.toPlanarPresentation
  thirdSide := fan.third.outwardSide presentation.toPlanarPresentation
  firstColor := fan.first.color
  secondColor := fan.second.color
  thirdColor := fan.third.color
  sidesNodup := fan.sidesNodup

theorem first_data
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    fan.first ∈ problem.contractedEndpoints ∧ fan.first.vertex = vertex := by
  rw [← contractedEndpointsAt_mem_iff problem vertex fan.first]
  rw [fan.endpoints_eq]
  simp

theorem second_data
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    fan.second ∈ problem.contractedEndpoints ∧ fan.second.vertex = vertex := by
  rw [← contractedEndpointsAt_mem_iff problem vertex fan.second]
  rw [fan.endpoints_eq]
  simp

theorem third_data
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    fan.third ∈ problem.contractedEndpoints ∧ fan.third.vertex = vertex := by
  rw [← contractedEndpointsAt_mem_iff problem vertex fan.third]
  rw [fan.endpoints_eq]
  simp

theorem endpoints_nodup
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex) :
    [fan.first, fan.second, fan.third].Nodup := by
  rw [← fan.endpoints_eq]
  exact contractedEndpointsAt_nodup problem degree vertex

theorem first_ne_second
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex) :
    fan.first ≠ fan.second := by
  intro equal
  have nodup := fan.endpoints_nodup degree
  exact (List.nodup_cons.mp nodup).1 (by simp [equal])

theorem first_ne_third
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex) :
    fan.first ≠ fan.third := by
  intro equal
  have nodup := fan.endpoints_nodup degree
  exact (List.nodup_cons.mp nodup).1 (by simp [equal])

theorem second_ne_third
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (degree : problem.DegreeTwoOrThree)
    (fan : ContractedVertexFan presentation vertex) :
    fan.second ≠ fan.third := by
  intro equal
  have nodup := fan.endpoints_nodup degree
  have tailNodup := (List.nodup_cons.mp nodup).2
  exact (List.nodup_cons.mp tailNodup).1 (by simp [equal])

end ContractedVertexFan

/-- Any explicitly named three-entry endpoint list determines a contracted
vertex fan. -/
theorem exists_contractVertexFan_of_endpoints_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (vertex : PeriodicThreeDMVertex)
    (first second third : ContractedEndpoint)
    (endpointsEq :
      problem.contractedEndpointsAt vertex = [first, second, third]) :
    Nonempty (ContractedVertexFan presentation vertex) := by
  have firstAt : first ∈ problem.contractedEndpointsAt vertex := by
    rw [endpointsEq]
    simp
  have secondAt : second ∈ problem.contractedEndpointsAt vertex := by
    rw [endpointsEq]
    simp
  have thirdAt : third ∈ problem.contractedEndpointsAt vertex := by
    rw [endpointsEq]
    simp
  have firstData :=
    (contractedEndpointsAt_mem_iff problem vertex first).mp firstAt
  have secondData :=
    (contractedEndpointsAt_mem_iff problem vertex second).mp secondAt
  have thirdData :=
    (contractedEndpointsAt_mem_iff problem vertex third).mp thirdAt
  have endpointsNodup : [first, second, third].Nodup := by
    rw [← endpointsEq]
    exact contractedEndpointsAt_nodup problem degree vertex
  have firstSecond : first ≠ second := by
    intro equal
    subst second
    simp at endpointsNodup
  have firstThird : first ≠ third := by
    intro equal
    subst third
    simp at endpointsNodup
  have secondThird : second ≠ third := by
    intro equal
    subst third
    simp at endpointsNodup
  have firstSecondSide := first.outwardSide_ne presentation degree
    firstData.1 secondData.1 firstSecond
    (firstData.2.trans secondData.2.symm)
  have firstThirdSide := first.outwardSide_ne presentation degree
    firstData.1 thirdData.1 firstThird
    (firstData.2.trans thirdData.2.symm)
  have secondThirdSide := second.outwardSide_ne presentation degree
    secondData.1 thirdData.1 secondThird
    (secondData.2.trans thirdData.2.symm)
  exact ⟨{
    first := first
    second := second
    third := third
    endpoints_eq := endpointsEq
    sidesNodup := by
      simp [firstSecondSide, firstThirdSide, secondThirdSide]
  }⟩

/-- A list of length three can be named by its entries. -/
theorem exists_eq_triple_of_length_eq_three
    {α : Type*} (items : List α) (length : items.length = 3) :
    ∃ first second third, items = [first, second, third] := by
  rcases items with _ | ⟨first, items⟩
  · simp at length
  rcases items with _ | ⟨second, items⟩
  · simp at length
  rcases items with _ | ⟨third, items⟩
  · simp at length
  rcases items with _ | ⟨fourth, items⟩
  · exact ⟨first, second, third, rfl⟩
  · simp at length

/-- Every in-range triple vertex has a geometric contracted fan. -/
theorem exists_contractVertexFan_at_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    Nonempty
      (ContractedVertexFan presentation (.triple tripleIndex)) := by
  obtain ⟨first, second, third, endpointsEq⟩ :=
    exists_contractedEndpointsAt_triple_eq
      problem wellFormed degree tripleIndex indexLt
  exact exists_contractVertexFan_of_endpoints_eq
    presentation degree (.triple tripleIndex)
      first second third endpointsEq

/-- Every retained degree-three element vertex has a geometric contracted
fan. -/
theorem exists_contractVertexFan_at_element
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3) :
    Nonempty (ContractedVertexFan presentation (.element color atom)) := by
  obtain ⟨first, second, third, endpointsEq⟩ :=
    exists_eq_triple_of_length_eq_three
      (problem.contractedEndpointsAt (.element color atom))
      (contractedEndpointsAt_element_length problem color atom
        atomLt degreeThree)
  exact exists_contractVertexFan_of_endpoints_eq
    presentation degreeTwoOrThree (.element color atom)
      first second third endpointsEq

/-- A triple endpoint carries its RGB incidence tag in its owning
contracted edge. -/
theorem ContractedEndpoint.incidenceTag_mem_of_vertex_eq_triple
    (endpoint : ContractedEndpoint) (tripleIndex : Nat)
    (vertexEq : endpoint.vertex = .triple tripleIndex) :
    (⟨tripleIndex, endpoint.color⟩ : IncidenceTag) ∈
      endpoint.edge.incidenceTags := by
  cases endpoint with
  | source edge =>
      cases edge <;>
        simp_all [ContractedEndpoint.vertex, ContractedEndpoint.edge,
          ContractedEndpoint.color, ContractedEdge.toPeriodicEdge,
          ContractedEdge.incidenceTags, ContractedEdge.sourceTag,
          ContractedEdge.targetTag]
  | target edge =>
      cases edge <;>
        simp_all [ContractedEndpoint.vertex, ContractedEndpoint.edge,
          ContractedEndpoint.color, ContractedEdge.toPeriodicEdge,
          ContractedEdge.incidenceTags, ContractedEdge.sourceTag,
          ContractedEdge.targetTag]

/-- Distinct endpoints at one triple vertex have distinct edge colors. -/
theorem ContractedEndpoint.color_ne_of_vertex_eq_triple
    {problem : PeriodicThreeDM}
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (tripleIndex : Nat)
    (firstVertex : first.vertex = .triple tripleIndex)
    (secondVertex : second.vertex = .triple tripleIndex) :
    first.color ≠ second.color := by
  intro colorsEqual
  have edgesDifferent := first.edge_ne_of_ne_of_vertex_eq degree
    firstMember secondMember different
    (firstVertex.trans secondVertex.symm)
  apply edgesDifferent
  apply contractedEdges_eq_of_common_incidenceTag problem degree
    (first.edge_mem_of_mem firstMember)
    (second.edge_mem_of_mem secondMember)
    (tag := ⟨tripleIndex, first.color⟩)
  · exact first.incidenceTag_mem_of_vertex_eq_triple
      tripleIndex firstVertex
  · simpa [colorsEqual] using
      second.incidenceTag_mem_of_vertex_eq_triple
        tripleIndex secondVertex

/-- The three colors packaged at a triple fan are pairwise distinct. -/
theorem ContractedVertexFan.colors_nodup_of_triple
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (fan : ContractedVertexFan presentation (.triple tripleIndex)) :
    [fan.coloredFan.firstColor, fan.coloredFan.secondColor,
      fan.coloredFan.thirdColor].Nodup := by
  have firstSecond := fan.first.color_ne_of_vertex_eq_triple degree
    fan.first_data.1 fan.second_data.1 (fan.first_ne_second degree)
    tripleIndex fan.first_data.2 fan.second_data.2
  have firstThird := fan.first.color_ne_of_vertex_eq_triple degree
    fan.first_data.1 fan.third_data.1 (fan.first_ne_third degree)
    tripleIndex fan.first_data.2 fan.third_data.2
  have secondThird := fan.second.color_ne_of_vertex_eq_triple degree
    fan.second_data.1 fan.third_data.1 (fan.second_ne_third degree)
    tripleIndex fan.second_data.2 fan.third_data.2
  simp [coloredFan, firstSecond, firstThird, secondThird]

/-- An endpoint at a retained element vertex inherits that element's
color. -/
theorem ContractedEndpoint.color_eq_of_vertex_eq_element
    (endpoint : ContractedEndpoint) (color : WireColor) (atom : Nat)
    (vertexEq : endpoint.vertex = .element color atom) :
    endpoint.color = color := by
  cases endpoint with
  | source edge =>
      cases edge <;>
        simp_all [ContractedEndpoint.vertex, ContractedEdge.toPeriodicEdge]
  | target edge =>
      cases edge <;>
        simp_all [ContractedEndpoint.vertex, ContractedEndpoint.color,
          ContractedEndpoint.edge, ContractedEdge.toPeriodicEdge]

/-- A retained element fan is monochromatic. -/
theorem ContractedVertexFan.coloredFan_eq_monochromatic
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (color : WireColor) (atom : Nat)
    (fan : ContractedVertexFan presentation (.element color atom)) :
    fan.coloredFan.canonicalColoring = fun _ => color := by
  apply fan.coloredFan.canonicalColoring_eq_of_monochromatic color
  · exact fan.first.color_eq_of_vertex_eq_element
      color atom fan.first_data.2
  · exact fan.second.color_eq_of_vertex_eq_element
      color atom fan.second_data.2
  · exact fan.third.color_eq_of_vertex_eq_element
      color atom fan.third_data.2

end PeriodicThreeDM
end LeanTrominoes

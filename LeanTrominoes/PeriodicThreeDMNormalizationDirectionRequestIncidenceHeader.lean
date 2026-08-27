/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestElementHeaderData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestTripleHeaderData

/-! # Complete route-request headers from original incidence routes -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open NormalizationCompiler

/-- Canonical source-side data always comes from the source triple's three
RGB incidence routes. -/
def sourceIncidenceEndpointHeaderData
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    EndpointHeaderData :=
  incidenceColorEndpointHeaderData input
    edge.sourceIncidence.tripleIndex (.source edge)

/-- Canonical target-side data comes from an RGB triple fan for a suppressed
edge and from the three terminal incidence directions for a retained
monochromatic element. -/
def targetIncidenceEndpointHeaderData
    (input : NormalizationCompiler.Input) : ContractedEdge →
      EndpointHeaderData
  | .retained color atom incidence =>
      retainedElementEndpointHeaderData input color atom incidence
  | .through color atom first second =>
      incidenceColorEndpointHeaderData input
        second.tripleIndex (.target (.through color atom first second))

/-- Complete six-field header expressed only through original incidence
routes and finite local lookups. -/
def Header.ofIncidenceData
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) : Header :=
  Header.ofEndpointData
    (sourceIncidenceEndpointHeaderData input edge)
    (targetIncidenceEndpointHeaderData input edge)

theorem source_mem_contractedEndpoints_of_edge_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    ContractedEndpoint.source edge ∈ problem.contractedEndpoints := by
  unfold contractedEndpoints
  exact List.mem_flatMap.mpr ⟨edge, member, by simp⟩

theorem target_mem_contractedEndpoints_of_edge_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    ContractedEndpoint.target edge ∈ problem.contractedEndpoints := by
  unfold contractedEndpoints
  exact List.mem_flatMap.mpr ⟨edge, member, by simp⟩

/-- A globally enumerated edge's stored element index is in range. -/
theorem contractedEdge_atom_lt_of_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.atom < problem.elementCount edge.color := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, localMember⟩
  have metadata := contractedEdgesForElement_metadata
    problem color atom localMember
  rw [metadata.1, metadata.2]
  exact List.mem_range.mp atomMember

/-- Every request header in a compatible normalized presentation is exactly
the finite header reconstructed from original incidence-route endpoint
directions. -/
theorem ofEdge_header_eq_ofIncidenceData
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (edge : ContractedEdge)
    (edgeMember : edge ∈ problem.contractedEdges) :
    let input := inputOfPresentation presentation.toPlanarPresentation
    (ofEdge input edge).header = Header.ofIncidenceData input edge := by
  dsimp only
  let input := inputOfPresentation presentation.toPlanarPresentation
  have sourceEndpointMember :=
    source_mem_contractedEndpoints_of_edge_mem problem edgeMember
  have targetEndpointMember :=
    target_mem_contractedEndpoints_of_edge_mem problem edgeMember
  have edgeData := contractedEdge_incidence_members_of_mem
    problem edgeMember
  cases edge with
  | retained color atom incidence =>
      have incidenceMember :
          incidence ∈ problem.incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have tripleLt := incidence_tripleIndex_lt
        problem color atom incidenceMember
      have sourceChoices :=
        tripleEndpointHeaderChoices_eq_incidenceColorData
          presentation wellFormed degree incidence.tripleIndex tripleLt
          (.source (.retained color atom incidence))
          sourceEndpointMember rfl
      have atomLt :=
        contractedEdge_atom_lt_of_mem problem edgeMember
      have degreeThree : problem.degree color atom = 3 := by
        simpa [ContractedEdge.color, ContractedEdge.atom,
          ContractedEdge.targetIsElement] using edgeData.2.2
      have targetChoices :=
        retainedElementTargetHeaderChoices_eq_incidenceData
          presentation degree color atom atomLt degreeThree incidence
      rw [show inputOfPresentation presentation.toPlanarPresentation = input
        by rfl] at sourceChoices targetChoices ⊢
      rw [ofEdge_header_eq_ofEndpointData]
      unfold Header.ofIncidenceData Header.ofEndpointData
        sourceIncidenceEndpointHeaderData
        targetIncidenceEndpointHeaderData
      rw [sourceChoices.1, targetChoices.1,
        sourceChoices.2.1, targetChoices.2.1,
        sourceChoices.2.2, targetChoices.2.2]
      rfl
  | through color atom first second =>
      have firstMember : first ∈ problem.incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have secondMember : second ∈ problem.incidences color atom := by
        simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.2.1
      have firstLt := incidence_tripleIndex_lt
        problem color atom firstMember
      have secondLt := incidence_tripleIndex_lt
        problem color atom secondMember
      have sourceChoices :=
        tripleEndpointHeaderChoices_eq_incidenceColorData
          presentation wellFormed degree first.tripleIndex firstLt
          (.source (.through color atom first second))
          sourceEndpointMember rfl
      have targetChoices :=
        tripleEndpointHeaderChoices_eq_incidenceColorData
          presentation wellFormed degree second.tripleIndex secondLt
          (.target (.through color atom first second))
          targetEndpointMember rfl
      rw [show inputOfPresentation presentation.toPlanarPresentation = input
        by rfl] at sourceChoices targetChoices ⊢
      rw [ofEdge_header_eq_ofEndpointData]
      unfold Header.ofIncidenceData Header.ofEndpointData
        sourceIncidenceEndpointHeaderData
        targetIncidenceEndpointHeaderData
      rw [sourceChoices.1, targetChoices.1,
        sourceChoices.2.1, targetChoices.2.1,
        sourceChoices.2.2, targetChoices.2.2]
      rfl

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes

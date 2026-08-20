/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationIncidenceEndpointDirections
import LeanTrominoes.PeriodicThreeDMContractedTagEndpoints
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointDataComputability

/-! # Every contracted triple endpoint keeps its tagged incidence direction -/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Forget the outer color/atom grouping of a complete contracted-edge
membership witness. -/
theorem exists_contractedEdgesForElement_of_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    ∃ color atom,
      edge ∈ problem.contractedEdgesForElement color atom := by
  simp only [contractedEdges, List.mem_flatMap] at edgeMember
  rcases edgeMember with ⟨color, _, edgeMember⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at edgeMember
  rcases edgeMember with ⟨atom, _, localMember⟩
  exact ⟨color, atom, localMember⟩

/-- An enumerated endpoint based at a triple vertex is one of the retained
triple endpoints (and hence carries an original incidence tag). -/
theorem ContractedEndpoint.mem_contractedTripleEndpoints_of_vertex_triple
    {problem : PeriodicThreeDM} {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {tripleIndex : Nat}
    (vertexEq : endpoint.vertex = .triple tripleIndex) :
    endpoint ∈ problem.contractedTripleEndpoints := by
  have edgeMember := endpoint.edge_mem_of_mem endpointMember
  unfold contractedTripleEndpoints
  cases endpoint with
  | source edge =>
      apply List.mem_flatMap.mpr
      refine ⟨edge, edgeMember, ?_⟩
      cases edge <;> simp [ContractedEdge.tripleEndpoints]
  | target edge =>
      cases edge with
      | retained color atom incidence =>
          simp [ContractedEndpoint.vertex,
            ContractedEdge.toPeriodicEdge] at vertexEq
      | through color atom first second =>
          apply List.mem_flatMap.mpr
          refine ⟨ContractedEdge.through color atom first second,
            edgeMember, ?_⟩
          simp [ContractedEdge.tripleEndpoints]

@[simp] theorem ContractedEndpoint.incidenceTag_color
    (endpoint : ContractedEndpoint) :
    endpoint.incidenceTag.color = endpoint.color := by
  cases endpoint with
  | source edge => cases edge <;> rfl
  | target edge => cases edge <;> rfl

/-- Uniform form of the two endpoint lemmas: every listed contracted triple
endpoint points along the first segment of its represented original
incidence route. -/
theorem PlanarPresentation.compilerOutwardDirection_eq_incidenceTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint)
    (endpointMember : endpoint ∈ problem.contractedTripleEndpoints) :
    NormalizationCompiler.outwardDirection
        (NormalizationCompiler.inputOfPresentation presentation)
        endpoint =
      AxisDirection.polylineFirstDirection
        (NormalizationCompiler.incidenceRoute
          (NormalizationCompiler.inputOfPresentation presentation)
          endpoint.incidenceTag) := by
  simp only [contractedTripleEndpoints, List.mem_flatMap] at endpointMember
  rcases endpointMember with ⟨edge, edgeMember, endpointMember⟩
  rcases problem.exists_contractedEdgesForElement_of_mem edgeMember with
    ⟨generatedColor, generatedAtom, localMember⟩
  cases edge with
  | retained color atom incidence =>
      simp only [ContractedEdge.tripleEndpoints,
        List.mem_singleton] at endpointMember
      subst endpoint
      simpa [ContractedEndpoint.incidenceTag] using
        presentation.compilerOutwardDirection_source_eq_incidence
          generatedColor generatedAtom
          (.retained color atom incidence) localMember
  | through color atom first second =>
      simp only [ContractedEdge.tripleEndpoints, List.mem_cons,
        List.not_mem_nil, or_false] at endpointMember
      rcases endpointMember with rfl | rfl
      · simpa [ContractedEndpoint.incidenceTag] using
          presentation.compilerOutwardDirection_source_eq_incidence
            generatedColor generatedAtom
            (.through color atom first second) localMember
      · have metadata :=
          contractedEdgesForElement_metadata
            problem generatedColor generatedAtom localMember
        simp only [ContractedEdge.color,
          ContractedEdge.atom] at metadata
        rcases metadata with ⟨rfl, rfl⟩
        simpa [ContractedEndpoint.incidenceTag,
          ContractedEdge.targetTag] using
          presentation.compilerOutwardDirection_target_through_eq_incidence
            color atom first second localMember

/-- The same result after converting the incidence direction to the old
vertex-template side used by normalization. -/
theorem PlanarPresentation.compilerOutwardSide_eq_incidenceTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint)
    (endpointMember : endpoint ∈ problem.contractedTripleEndpoints) :
    NormalizationCompiler.outwardSide
        (NormalizationCompiler.inputOfPresentation presentation)
        endpoint =
      VertexSide.ofDirection
        (AxisDirection.polylineFirstDirection
          (NormalizationCompiler.incidenceRoute
            (NormalizationCompiler.inputOfPresentation presentation)
            endpoint.incidenceTag)) := by
  unfold NormalizationCompiler.outwardSide
  rw [presentation.compilerOutwardDirection_eq_incidenceTag
    endpoint endpointMember]

/-- Consequently the compressed side/color datum at a triple endpoint is
computed directly from its original incidence tag and route. -/
theorem PlanarPresentation.compilerEndpointSideColor_eq_incidenceTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint)
    (endpointMember : endpoint ∈ problem.contractedTripleEndpoints) :
    NormalizationCompiler.endpointSideColor
        (NormalizationCompiler.inputOfPresentation presentation,
          endpoint) =
      (VertexSide.ofDirection
        (AxisDirection.polylineFirstDirection
          (NormalizationCompiler.incidenceRoute
            (NormalizationCompiler.inputOfPresentation presentation)
            endpoint.incidenceTag)),
        endpoint.incidenceTag.color) := by
  unfold NormalizationCompiler.endpointSideColor
  rw [presentation.compilerOutwardSide_eq_incidenceTag
    endpoint endpointMember]
  simp

end PeriodicThreeDM
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractionOrientation
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationLift
import LeanTrominoes.PeriodicThreeDMNormalizationVertexPortCompleteness

/-!
# Orientation values at normalized contracted endpoints

This module supplies the finite endpoint lookup used at normalized
degree-three vertex cells.  It also expresses the inward value at either end
of a contracted edge in terms of the original suppressed 3DM orientation.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Read the inward value at a contracted endpoint using the lattice
translate of that endpoint's vertex. -/
def ContractedEndpoint.inwardAtVertexTranslate
    (values : IncidenceTag → Cell → Bool) :
    ContractedEndpoint → Cell → Bool
  | .source edge, translate => edge.sourceInward values translate
  | .target edge, translate => edge.targetInwardAtTarget values translate

@[simp]
theorem ContractedEndpoint.inwardAtVertexTranslate_source
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (translate : Cell) :
    (ContractedEndpoint.source edge).inwardAtVertexTranslate
        values translate =
      edge.sourceInward values translate := by
  rfl

@[simp]
theorem ContractedEndpoint.inwardAtVertexTranslate_target
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (translate : Cell) :
    (ContractedEndpoint.target edge).inwardAtVertexTranslate
        values translate =
      edge.targetInwardAtTarget values translate := by
  rfl

/-- At a triple endpoint, inward means the negation of the original
triple-to-element incidence value at the same triple translate. -/
theorem ContractedEndpoint.inwardAtVertexTranslate_eq_not_value_of_triple
    (values : IncidenceTag → Cell → Bool)
    (endpoint : ContractedEndpoint) (tripleIndex : Nat)
    (vertexEq : endpoint.vertex = .triple tripleIndex)
    (translate : Cell) :
    endpoint.inwardAtVertexTranslate values translate =
      !(values ⟨tripleIndex, endpoint.color⟩ translate) := by
  cases endpoint with
  | source edge =>
      cases edge <;>
        simp_all [ContractedEndpoint.vertex, ContractedEndpoint.color,
          ContractedEndpoint.edge, ContractedEndpoint.inwardAtVertexTranslate,
          ContractedEdge.toPeriodicEdge, ContractedEdge.sourceInward,
          ContractedEdge.sourceTag]
  | target edge =>
      cases edge with
      | retained color atom incidence =>
          simp [ContractedEndpoint.vertex, ContractedEdge.toPeriodicEdge]
            at vertexEq
      | through color atom first second =>
          simp only [ContractedEndpoint.vertex,
            ContractedEdge.toPeriodicEdge] at vertexEq
          injection vertexEq with indexEq
          subst tripleIndex
          simp [ContractedEndpoint.inwardAtVertexTranslate,
            ContractedEndpoint.color, ContractedEndpoint.edge,
            ContractedEdge.targetInwardAtTarget,
            ContractedEdge.targetInward, ContractedEdge.toPeriodicEdge,
            Cell.sub, Cell.add]

/-- At a retained colored-element endpoint, the inward value is the
original incidence value based at the corresponding source-triple
translate. -/
@[simp]
theorem ContractedEndpoint.inwardAtVertexTranslate_target_retained
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (elementTranslate : Cell) :
    (ContractedEndpoint.target
        (.retained color atom incidence)).inwardAtVertexTranslate
          values elementTranslate =
      values ⟨incidence.tripleIndex, color⟩
        (Cell.sub elementTranslate incidence.offset) := by
  rfl

private theorem List.find?_eq_some_of_mem_of_unique
    {α : Type*}
    (values : List α) (predicate : α → Bool) (selected : α)
    (member : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (unique :
      ∀ candidate ∈ values,
        predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      by_cases headTrue : predicate head = true
      · have headEq : head = selected :=
          unique head (by simp) headTrue
        subst head
        simp [selectedTrue]
      · have selectedTail : selected ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with selectedEq | selectedTail
          · subst head
            exact (headTrue selectedTrue).elim
          · exact selectedTail
        simp [headTrue]
        exact induction selectedTail fun candidate candidateMember =>
          unique candidate (by simp [candidateMember])

/-- Deterministically select the endpoint occupying one normalized port of a
prototype contracted vertex.  The fallback is irrelevant at exposed ports
of certified presentations. -/
def PlanarPresentation.endpointAtVertexPort
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) (side : Side) : ContractedEndpoint :=
  (problem.contractedEndpoints.find? fun endpoint =>
      decide (endpoint.vertex = vertex ∧
        (endpoint.finalNormalizedPort presentation).side = side)).getD
    defaultContractedTripleEndpoint

/-- Endpoint selection recovers every actual endpoint from its own vertex
and final normalized port. -/
theorem PlanarPresentation.endpointAtVertexPort_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints) :
    presentation.toPlanarPresentation.endpointAtVertexPort endpoint.vertex
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side =
      endpoint := by
  unfold PlanarPresentation.endpointAtVertexPort
  have found :
      problem.contractedEndpoints.find? (fun candidate =>
        decide (candidate.vertex = endpoint.vertex ∧
          (candidate.finalNormalizedPort
            presentation.toPlanarPresentation).side =
              (endpoint.finalNormalizedPort
                presentation.toPlanarPresentation).side)) =
        some endpoint := by
    apply List.find?_eq_some_of_mem_of_unique
      problem.contractedEndpoints _ endpoint endpointMember
    · simp
    · intro candidate candidateMember candidateTrue
      simp only [decide_eq_true_eq] at candidateTrue
      by_contra different
      have portsDifferent := candidate.finalNormalizedPort_ne
        presentation wellFormed degree candidateMember endpointMember
          different candidateTrue.1
      apply portsDifferent
      generalize candidatePortEq :
          candidate.finalNormalizedPort presentation.toPlanarPresentation =
            candidatePort at candidateTrue
      generalize endpointPortEq :
          endpoint.finalNormalizedPort presentation.toPlanarPresentation =
            endpointPort at candidateTrue
      cases candidatePort <;> cases endpointPort <;>
        simp_all [CanonicalVertexPort.side]
  rw [found]
  rfl

/-- Every exposed port selects a genuine endpoint with the advertised
vertex, side, and edge color. -/
theorem PlanarPresentation.endpointAtVertexPort_data_of_exposed
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    {side : Side} {color : WireColor}
    (exposed :
      (presentation.toPlanarPresentation.finalVertexCellType vertex).portColor
        side = some color) :
    let endpoint :=
      presentation.toPlanarPresentation.endpointAtVertexPort vertex side
    endpoint ∈ problem.contractedEndpoints ∧
      endpoint.vertex = vertex ∧
      (endpoint.finalNormalizedPort
        presentation.toPlanarPresentation).side = side ∧
      endpoint.color = color := by
  rcases PlanarPresentation.exists_endpoint_of_finalVertexCellType_portColor_eq_some
      presentation wellFormed degree vertexMember exposed with
    ⟨endpoint, endpointMember, endpointVertex, endpointSide, endpointColor⟩
  have selected := PlanarPresentation.endpointAtVertexPort_eq
    presentation wellFormed degree endpointMember
  rw [endpointVertex, endpointSide] at selected
  simpa [selected] using
    And.intro endpointMember
      (And.intro endpointVertex (And.intro endpointSide endpointColor))

/-- Inward value exposed by one normalized vertex port at a given lattice
translate. -/
def PlanarPresentation.vertexPortInward
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (values : problem.GraphOrientation)
    (vertex : PeriodicThreeDMVertex) (translate : Cell)
    (side : Side) : Bool :=
  (presentation.endpointAtVertexPort vertex side).inwardAtVertexTranslate
    values translate

/-- At an actual endpoint's port, `vertexPortInward` is exactly that
endpoint's contracted inward value. -/
theorem PlanarPresentation.vertexPortInward_endpoint
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    (translate : Cell) :
    presentation.toPlanarPresentation.vertexPortInward values endpoint.vertex
        translate
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side =
      endpoint.inwardAtVertexTranslate values translate := by
  unfold PlanarPresentation.vertexPortInward
  rw [PlanarPresentation.endpointAtVertexPort_eq
    presentation wellFormed degree endpointMember]

end PeriodicThreeDM

end LeanTrominoes

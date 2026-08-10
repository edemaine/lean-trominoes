import LeanTrominoes.PeriodicThreeDMContractionCoverage
import LeanTrominoes.PeriodicThreeDMContractedEndpointFans

/-!
# Triple endpoints represented by contracted 3DM edges

A retained edge represents one original incidence tag at its source triple,
while a through edge represents one tag at each triple endpoint.  This module
packages those endpoint occurrences as a duplicate-free list and proves that
their tags are a permutation of the original incidence-tag enumeration.
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- The original incidence tag represented at either syntactic endpoint. -/
def ContractedEndpoint.incidenceTag : ContractedEndpoint → IncidenceTag
  | .source edge => edge.sourceTag
  | .target edge => edge.targetTag

/-- Exactly the triple endpoints of one contracted edge.  A retained edge's
target is a colored element and is therefore omitted. -/
def ContractedEdge.tripleEndpoints (edge : ContractedEdge) :
    List ContractedEndpoint :=
  match edge with
  | .retained .. => [.source edge]
  | .through .. => [.source edge, .target edge]

/-- All triple endpoint occurrences in contracted-edge order. -/
def contractedTripleEndpoints (problem : PeriodicThreeDM) :
    List ContractedEndpoint :=
  problem.contractedEdges.flatMap ContractedEdge.tripleEndpoints

/-- Mapping one edge's triple endpoints to tags recovers its stored incidence
metadata exactly. -/
theorem ContractedEdge.map_incidenceTag_tripleEndpoints
    (edge : ContractedEdge) :
    edge.tripleEndpoints.map ContractedEndpoint.incidenceTag =
      edge.incidenceTags := by
  cases edge <;> rfl

/-- The complete endpoint enumeration maps exactly to the flattened
contracted incidence-tag list. -/
theorem contractedTripleEndpoints_map_incidenceTag
    (problem : PeriodicThreeDM) :
    problem.contractedTripleEndpoints.map
        ContractedEndpoint.incidenceTag =
      problem.contractedIncidenceTags := by
  simp only [contractedTripleEndpoints, contractedIncidenceTags,
    List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro edge edgeMember
  exact edge.map_incidenceTag_tripleEndpoints

/-- Under the degree promise, no triple endpoint occurrence is listed twice. -/
theorem contractedTripleEndpoints_nodup
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    problem.contractedTripleEndpoints.Nodup := by
  apply List.Nodup.of_map ContractedEndpoint.incidenceTag
  rw [problem.contractedTripleEndpoints_map_incidenceTag]
  exact contractedIncidenceTags_nodup problem degree

/-- Triple endpoint tags are exactly the original incidence tags. -/
theorem contractedTripleEndpoint_tag_mem_iff
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tag : IncidenceTag) :
    (∃ endpoint ∈ problem.contractedTripleEndpoints,
        endpoint.incidenceTag = tag) ↔
      tag ∈ problem.incidenceTags := by
  rw [← problem.contractedIncidenceTags_perm wellFormed degree |>.mem_iff]
  rw [← problem.contractedTripleEndpoints_map_incidenceTag]
  simp

/-- Every original incidence tag has a unique contracted triple endpoint. -/
theorem exists_unique_contractedTripleEndpoint
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag}
    (tagMember : tag ∈ problem.incidenceTags) :
    ∃! endpoint,
      endpoint ∈ problem.contractedTripleEndpoints ∧
        endpoint.incidenceTag = tag := by
  rcases (problem.contractedTripleEndpoint_tag_mem_iff
      wellFormed degree tag).mpr tagMember with
    ⟨endpoint, endpointMember, endpointTag⟩
  refine ⟨endpoint, ⟨endpointMember, endpointTag⟩, ?_⟩
  intro other otherData
  have tagsNodup :
      (problem.contractedTripleEndpoints.map
        ContractedEndpoint.incidenceTag).Nodup := by
    rw [problem.contractedTripleEndpoints_map_incidenceTag]
    exact contractedIncidenceTags_nodup problem degree
  exact (List.inj_on_of_nodup_map tagsNodup endpointMember otherData.1
    (endpointTag.trans otherData.2.symm)).symm

/-- A harmless fallback used only for incidence tags outside a problem's
finite presentation.  Valid tags are proved below never to select it unless
it is itself the genuine endpoint. -/
def defaultContractedTripleEndpoint : ContractedEndpoint :=
  .source (.retained .red 0 ⟨0, (0, 0)⟩)

/-- Executably select the first contracted triple endpoint carrying a given
original incidence tag. -/
def contractedTripleEndpointForTag (problem : PeriodicThreeDM)
    (tag : IncidenceTag) : ContractedEndpoint :=
  (problem.contractedTripleEndpoints.find? fun endpoint =>
      decide (endpoint.incidenceTag = tag)).getD
    defaultContractedTripleEndpoint

/-- Every valid incidence tag's selected endpoint belongs to the complete
contracted triple-endpoint enumeration. -/
theorem contractedTripleEndpointForTag_mem
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag}
    (tagMember : tag ∈ problem.incidenceTags) :
    problem.contractedTripleEndpointForTag tag ∈
      problem.contractedTripleEndpoints := by
  unfold contractedTripleEndpointForTag
  generalize foundEq :
      problem.contractedTripleEndpoints.find? (fun endpoint =>
        decide (endpoint.incidenceTag = tag)) = found
  cases found with
  | some endpoint =>
      simp only [Option.getD_some]
      exact List.mem_of_find?_eq_some foundEq
  | none =>
      rcases (problem.contractedTripleEndpoint_tag_mem_iff
          wellFormed degree tag).mpr tagMember with
        ⟨endpoint, endpointMember, endpointTag⟩
      have predicateFalse :=
        List.find?_eq_none.mp foundEq endpoint endpointMember
      simp [endpointTag] at predicateFalse

/-- Every valid incidence tag is recovered exactly from its selected
contracted triple endpoint. -/
theorem contractedTripleEndpointForTag_incidenceTag
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag}
    (tagMember : tag ∈ problem.incidenceTags) :
    (problem.contractedTripleEndpointForTag tag).incidenceTag = tag := by
  unfold contractedTripleEndpointForTag
  generalize foundEq :
      problem.contractedTripleEndpoints.find? (fun endpoint =>
        decide (endpoint.incidenceTag = tag)) = found
  cases found with
  | some endpoint =>
      simp only [Option.getD_some]
      have predicateTrue := List.find?_some foundEq
      simpa using predicateTrue
  | none =>
      rcases (problem.contractedTripleEndpoint_tag_mem_iff
          wellFormed degree tag).mpr tagMember with
        ⟨endpoint, endpointMember, endpointTag⟩
      have predicateFalse :=
        List.find?_eq_none.mp foundEq endpoint endpointMember
      simp [endpointTag] at predicateFalse

/-- The executable selector agrees with any endpoint known to carry the
requested valid tag. -/
theorem contractedTripleEndpointForTag_eq
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag}
    (tagMember : tag ∈ problem.incidenceTags)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedTripleEndpoints)
    (endpointTag : endpoint.incidenceTag = tag) :
    problem.contractedTripleEndpointForTag tag = endpoint := by
  have selectedMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree tagMember
  have selectedTag := problem.contractedTripleEndpointForTag_incidenceTag
    wellFormed degree tagMember
  exact List.inj_on_of_nodup_map
    (by
      rw [problem.contractedTripleEndpoints_map_incidenceTag]
      exact contractedIncidenceTags_nodup problem degree)
    selectedMember endpointMember (selectedTag.trans endpointTag.symm)

end PeriodicThreeDM

end LeanTrominoes

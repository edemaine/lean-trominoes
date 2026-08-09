import LeanTrominoes.PeriodicThreeDMContractedEndpointFans

/-!
# Degree of contracted endpoint fans

The local normalization templates require exactly three ends at every
retained vertex.  This module proves the trichromatic half of that fact.
Contracted edge metadata is a permutation of the original RGB incidence
tags, so every indexed triple still has exactly three endpoint occurrences
after all degree-two colored vertices are suppressed.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Filtering a finite list by a mapped value counts the same occurrences as
`List.count` after mapping. -/
theorem length_filter_map_eq_count
    {α β : Type*} [DecidableEq β]
    (items : List α) (value : β) (project : α → β) :
    (items.filter fun item => project item = value).length =
      (items.map project).count value := by
  induction items with
  | nil => rfl
  | cons item rest induction =>
      by_cases equal : project item = value
      · simp [equal, induction]
      · simp [equal, induction]

/-- The length of the endpoint fan at a prototype vertex is its ordinary
graph-theoretic degree, with loops counted twice. -/
theorem contractedEndpointsAt_length_eq_degree
    (problem : PeriodicThreeDM)
    (vertex : PeriodicThreeDMVertex) :
    (problem.contractedEndpointsAt vertex).length =
      problem.contractedGraph.incidences.count vertex := by
  rw [contractedEndpointsAt, length_filter_map_eq_count,
    contractedEndpoints_vertices]

/-- Counting triple endpoints in the contracted graph is the same as
counting the triple indices stored in contracted incidence metadata. -/
theorem contractedGraph_triple_degree_eq_tag_count
    (problem : PeriodicThreeDM) (tripleIndex : Nat) :
    problem.contractedGraph.incidences.count (.triple tripleIndex) =
      (problem.contractedIncidenceTags.map fun tag =>
        PeriodicThreeDMVertex.triple tag.tripleIndex).count
          (.triple tripleIndex) := by
  unfold contractedGraph PeriodicGraph.incidences contractedIncidenceTags
  rw [List.flatMap_map, List.map_flatMap]
  let edges := problem.contractedEdges
  change
    (edges.flatMap fun edge => edge.toPeriodicEdge.incidences).count
        (.triple tripleIndex) =
      (edges.flatMap fun edge =>
        edge.incidenceTags.map fun tag =>
          PeriodicThreeDMVertex.triple tag.tripleIndex).count
        (.triple tripleIndex)
  induction edges with
  | nil => rfl
  | cons edge rest induction =>
      simp only [List.flatMap_cons, List.count_append]
      rw [induction]
      congr 1
      cases edge <;> rfl

/-- The three RGB tags belonging to an in-range triple index contribute
exactly three copies of that triple vertex. -/
theorem incidenceTags_triple_count_eq_three
    (problem : PeriodicThreeDM) (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    (problem.incidenceTags.map fun tag =>
      PeriodicThreeDMVertex.triple tag.tripleIndex).count
        (.triple tripleIndex) = 3 := by
  rw [incidenceTags_eq_range_flatMap, List.map_flatMap]
  have countRange : ∀ bound : Nat,
      ((List.range bound).flatMap fun index =>
        (tripleIncidenceTags index).map fun tag =>
          PeriodicThreeDMVertex.triple tag.tripleIndex).count
          (.triple tripleIndex) =
        if tripleIndex < bound then 3 else 0 := by
    intro bound
    induction bound with
    | zero => simp
    | succ bound induction =>
        rw [List.range_succ, List.flatMap_append,
          List.count_append, induction]
        by_cases below : tripleIndex < bound
        · have different : bound ≠ tripleIndex := by omega
          simp [below, Nat.lt_succ_of_lt below, different,
            tripleIncidenceTags, incidenceColors]
        · by_cases equal : tripleIndex = bound
          · subst bound
            simp [tripleIncidenceTags, incidenceColors]
          · have notBelowSucc : ¬tripleIndex < bound + 1 := by omega
            have different : bound ≠ tripleIndex := fun same => equal same.symm
            simp [below, different, notBelowSucc,
              tripleIncidenceTags, incidenceColors]
  rw [countRange problem.triples.length, if_pos indexLt]

/-- Every indexed triple vertex retains degree exactly three after
suppression. -/
theorem contractedGraph_triple_degree_eq_three
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    problem.contractedGraph.incidences.count (.triple tripleIndex) = 3 := by
  rw [contractedGraph_triple_degree_eq_tag_count]
  have permuted :=
    (contractedIncidenceTags_perm problem wellFormed degree).map fun tag =>
      PeriodicThreeDMVertex.triple tag.tripleIndex
  rw [permuted.count_eq]
  exact incidenceTags_triple_count_eq_three problem tripleIndex indexLt

/-- Hence the executable endpoint list at every indexed trichromatic vertex
has exactly three entries. -/
theorem contractedEndpointsAt_triple_length
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    (problem.contractedEndpointsAt (.triple tripleIndex)).length = 3 := by
  rw [contractedEndpointsAt_length_eq_degree]
  exact contractedGraph_triple_degree_eq_three
    problem wellFormed degree tripleIndex indexLt

/-- A three-entry endpoint fan can be named explicitly in its enumeration
order. -/
theorem exists_contractedEndpointsAt_triple_eq
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    ∃ first second third,
      problem.contractedEndpointsAt (.triple tripleIndex) =
        [first, second, third] := by
  generalize equation :
      problem.contractedEndpointsAt (.triple tripleIndex) = endpoints
  have length : endpoints.length = 3 := by
    rw [← equation]
    exact contractedEndpointsAt_triple_length
      problem wellFormed degree tripleIndex indexLt
  rcases endpoints with _ | ⟨first, endpoints⟩
  · simp at length
  rcases endpoints with _ | ⟨second, endpoints⟩
  · simp at length
  rcases endpoints with _ | ⟨third, endpoints⟩
  · simp at length
  rcases endpoints with _ | ⟨fourth, endpoints⟩
  · exact ⟨first, second, third, rfl⟩
  · simp at length

end PeriodicThreeDM
end LeanTrominoes

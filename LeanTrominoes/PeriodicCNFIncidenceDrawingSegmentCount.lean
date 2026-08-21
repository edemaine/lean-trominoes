/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaBackwardCoreExtras
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFIncidencePortSegmentExtraSum
import LeanTrominoes.PeriodicCNFIncidenceRouteSegmentCount
import LeanTrominoes.PeriodicOrthocrossingIndexedSegmentsLength

/-! # Exact segment count of a forward-local CNF incidence drawing -/

namespace LeanTrominoes
namespace PeriodicCNF

open UnaryProgramClauseProfile

/-- Segment contribution read from one clause's finite literal profiles,
excluding the variable-side fanout contribution. -/
def literalProfilesRouteSegmentCount
    (profiles : List LiteralProfile) : Nat :=
  5 * profiles.length +
    PeriodicOrthocrossing.portSegmentExtrasForDegree profiles.length +
    literalProfilesBackwardCoreExtras profiles

def ClauseProfile.routeSegmentCount (profile : ClauseProfile) : Nat :=
  literalProfilesRouteSegmentCount profile.literals

theorem incidenceDrawing_indexedSegments_length
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    (PeriodicOrthocrossing.drawing
      formula.incidenceGraph).indexedSegments.length =
      (formula.clauses.map fun clause =>
        literalProfilesRouteSegmentCount
          (ClauseProfileOccurrenceSplit.literalProfiles clause)).sum +
        2 * formula.variableOccurrences.dedup.length := by
  let graph := formula.incidenceGraph
  let endpointExtra := fun tagged :
      PeriodicEdge (CNFVertex Variable) × Nat =>
    PeriodicOrthocrossing.portSegmentExtra
        (PeriodicOrthocrossing.portRank graph
          (PeriodicOrthocrossing.sourcePort tagged.1 tagged.2)) +
      PeriodicOrthocrossing.portSegmentExtra
        (PeriodicOrthocrossing.portRank graph
          (PeriodicOrthocrossing.targetPort tagged.1 tagged.2))
  let backwardExtra := fun tagged :
      PeriodicEdge (CNFVertex Variable) × Nat =>
    PeriodicOrthocrossing.backwardCoreSegmentExtra tagged.1.offset
  rw [PeriodicOrthocrossing.drawing_indexedSegments_length_eq_routes]
  have routeCounts :
      graph.edges.zipIdx.map (fun tagged =>
        (gridPolylineSegments
          (PeriodicOrthocrossing.constructedEdgeRoute
            graph tagged.1 tagged.2)).length) =
        graph.edges.zipIdx.map (fun tagged =>
          5 + endpointExtra tagged + backwardExtra tagged) := by
    apply List.map_congr_left
    intro tagged taggedMember
    have count :=
      PeriodicOrthocrossing.taggedIncidence_route_segments_length
        formula forward degree tagged taggedMember
    dsimp [graph, endpointExtra, backwardExtra] at count ⊢
    omega
  rw [routeCounts]
  have split :
      (graph.edges.zipIdx.map fun tagged =>
        5 + endpointExtra tagged + backwardExtra tagged).sum =
        5 * graph.edges.length +
          (graph.edges.zipIdx.map endpointExtra).sum +
          (graph.edges.zipIdx.map backwardExtra).sum := by
    have general : ∀ values :
        List (PeriodicEdge (CNFVertex Variable) × Nat),
        (values.map fun tagged =>
          5 + endpointExtra tagged + backwardExtra tagged).sum =
          5 * values.length +
            (values.map endpointExtra).sum +
            (values.map backwardExtra).sum := by
      intro values
      induction values with
      | nil => rfl
      | cons tagged values induction =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [induction]
          omega
    simpa using general graph.edges.zipIdx
  rw [split]
  have endpoints :
      (graph.edges.zipIdx.map endpointExtra).sum =
        (formula.clauses.map fun clause =>
          PeriodicOrthocrossing.portSegmentExtrasForDegree
            clause.length).sum +
          2 * formula.variableOccurrences.dedup.length := by
    exact
      PeriodicOrthocrossing.incidenceGraph_portSegmentExtra_sum_of_count_eq_three
        formula exact
  rw [endpoints]
  have backwards :
      (graph.edges.zipIdx.map backwardExtra).sum =
        (formula.clauses.map fun clause =>
          literalProfilesBackwardCoreExtras
            (ClauseProfileOccurrenceSplit.literalProfiles clause)).sum := by
    change (graph.edges.zipIdx.map fun tagged =>
      PeriodicOrthocrossing.backwardCoreSegmentExtra
        tagged.1.offset).sum = _
    rw [show graph.edges.zipIdx.map (fun tagged =>
        PeriodicOrthocrossing.backwardCoreSegmentExtra tagged.1.offset) =
      (graph.edges.zipIdx.map Prod.fst).map (fun edge =>
        PeriodicOrthocrossing.backwardCoreSegmentExtra edge.offset) by
          rw [List.map_map]
          rfl,
      List.zipIdx_map_fst]
    exact incidenceGraph_backwardCoreExtra_sum formula forward
  rw [backwards, PeriodicCNF.incidenceGraph_edges_length]
  have literalCount :
      presentationLiteralCount formula =
        (formula.clauses.map List.length).sum := by
    simp [presentationLiteralCount]
  rw [literalCount]
  have clauseSum :
      (formula.clauses.map fun clause =>
        literalProfilesRouteSegmentCount
          (ClauseProfileOccurrenceSplit.literalProfiles clause)).sum =
        5 * (formula.clauses.map List.length).sum +
          (formula.clauses.map fun clause =>
            PeriodicOrthocrossing.portSegmentExtrasForDegree
              clause.length).sum +
          (formula.clauses.map fun clause =>
            literalProfilesBackwardCoreExtras
              (ClauseProfileOccurrenceSplit.literalProfiles clause)).sum := by
    induction formula.clauses with
    | nil => rfl
    | cons clause clauses induction =>
        simp only [List.map_cons, List.sum_cons]
        rw [induction]
        simp [literalProfilesRouteSegmentCount,
          ClauseProfileOccurrenceSplit.literalProfiles]
        omega
  rw [clauseSum]
  omega

/-- Any correct finite clause-profile stream therefore determines the exact
semantic drawing segment count. -/
theorem incidenceDrawing_indexedSegments_length_of_profiles
    {Variable : Type} [DecidableEq Variable]
    (profiles : List ClauseProfile)
    (formula : PeriodicCNF Variable)
    (profilesCorrect :
      profiles.map ClauseProfile.literals =
        formula.clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles)
    (forward : formula.IsForwardLocal)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    (PeriodicOrthocrossing.drawing
      formula.incidenceGraph).indexedSegments.length =
      (profiles.map ClauseProfile.routeSegmentCount).sum +
        2 * formula.variableOccurrences.dedup.length := by
  rw [incidenceDrawing_indexedSegments_length
    formula forward degree exact]
  congr 1
  unfold ClauseProfile.routeSegmentCount
  rw [show profiles.map (fun profile =>
      literalProfilesRouteSegmentCount profile.literals) =
    (profiles.map ClauseProfile.literals).map
      literalProfilesRouteSegmentCount by
        rw [List.map_map]
        rfl,
    profilesCorrect,
    List.map_map]
  simp [Function.comp_def]

end PeriodicCNF
end LeanTrominoes

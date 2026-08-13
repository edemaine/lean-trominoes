/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A bend record with its explicit translated-route occurrence erased. -/
def RouteBend.eraseTranslation (routeBend : RouteBend) : RouteBend :=
  { routeBend with translate := (0, 0) }

/-- The route geometry at a fixed segment index does not depend on which
translated occurrence was enumerated. -/
theorem routeBendsAux_eraseTranslation_eq_of_index_eq
    (routeIndex : Nat) :
    ∀ (points : List Cell) (startIndex : Nat)
      (firstTranslate secondTranslate : Cell)
      {first second : RouteBend},
      first ∈
          routeBendsAux routeIndex firstTranslate startIndex points →
        second ∈
          routeBendsAux routeIndex secondTranslate startIndex points →
        first.incomingSegmentIndex =
          second.incomingSegmentIndex →
        first.eraseTranslation = second.eraseTranslation := by
  intro points
  induction points with
  | nil =>
      intro startIndex firstTranslate secondTranslate first second firstMem
      simp [routeBendsAux] at firstMem
  | cons firstPoint rest induction =>
      cases rest with
      | nil =>
          intro startIndex firstTranslate secondTranslate first second firstMem
          simp [routeBendsAux] at firstMem
      | cons secondPoint rest =>
          cases rest with
          | nil =>
              intro startIndex firstTranslate secondTranslate first second
                firstMem
              simp [routeBendsAux] at firstMem
          | cons thirdPoint rest =>
              intro startIndex firstTranslate secondTranslate first second
                firstMem secondMem indexEq
              simp only [routeBendsAux, List.mem_cons]
                at firstMem secondMem
              rcases firstMem with firstEq | firstMem <;>
                rcases secondMem with secondEq | secondMem
              · subst first
                subst second
                rfl
              · subst first
                have secondData :=
                  routeBendsAux_member_data routeIndex secondTranslate
                    (secondPoint :: thirdPoint :: rest)
                    (startIndex + 1) secondMem
                simp at indexEq
                omega
              · subst second
                have firstData :=
                  routeBendsAux_member_data routeIndex firstTranslate
                    (secondPoint :: thirdPoint :: rest)
                    (startIndex + 1) firstMem
                simp at indexEq
                omega
              · exact induction (startIndex + 1)
                  firstTranslate secondTranslate
                  firstMem secondMem indexEq

/-- Route index and incoming-segment index determine the bend geometry
modulo explicit route translation. -/
theorem drawingRouteBends_eraseTranslation_eq_of_identity_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (routeEq : first.routeIndex = second.routeIndex)
    (indexEq :
      first.incomingSegmentIndex =
        second.incomingSegmentIndex) :
    first.eraseTranslation = second.eraseTranslation := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstTaggedRoute, firstTaggedRouteMem, firstTranslateMem⟩
  rcases List.mem_flatMap.mp firstTranslateMem with
    ⟨firstTranslate, _firstTranslateMem, firstBendMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondTaggedRoute, secondTaggedRouteMem, secondTranslateMem⟩
  rcases List.mem_flatMap.mp secondTranslateMem with
    ⟨secondTranslate, _secondTranslateMem, secondBendMem⟩
  have firstData :=
    routeBendsAux_member_data firstTaggedRoute.2 firstTranslate
      firstTaggedRoute.1 0 firstBendMem
  have secondData :=
    routeBendsAux_member_data secondTaggedRoute.2 secondTranslate
      secondTaggedRoute.1 0 secondBendMem
  have taggedRouteEq :
      firstTaggedRoute = secondTaggedRoute :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstTaggedRouteMem secondTaggedRouteMem
      (firstData.1.symm.trans
        (routeEq.trans secondData.1))
  subst secondTaggedRoute
  exact
    routeBendsAux_eraseTranslation_eq_of_index_eq
      firstTaggedRoute.2 firstTaggedRoute.1 0
      firstTranslate secondTranslate
      firstBendMem secondBendMem indexEq

/-- Normalizing a bend equality erases its common route translation. -/
theorem RouteBend.normalize_equalityLink_eq_eraseTranslation
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (routeBend.equalityLink graph) =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (routeBend.eraseTranslation.equalityLink graph) := by
  rcases routeBend with
    ⟨routeIndex, incomingSegmentIndex, translate,
      incomingStart, bend, outgoingFinish⟩
  simp [RouteBend.eraseTranslation, RouteBend.equalityLink,
    RouteBend.incomingTerminal, RouteBend.outgoingTerminal,
    PeriodicEquality.normalizeLink, normalizeCarrierNode,
    Cell.sub]

@[simp]
theorem RouteBend.normalize_equalityLink_first
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
      (routeBend.equalityLink graph)).first =
        .terminal routeBend.incomingTerminal.indexed .finish := by
  rfl

@[simp]
theorem RouteBend.normalize_equalityLink_second
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
      (routeBend.equalityLink graph)).second =
        .terminal routeBend.outgoingTerminal.indexed .start := by
  rfl

@[simp]
theorem RouteBend.normalize_equalityLink_relativeOffset
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
      (routeBend.equalityLink graph)).relativeOffset = (0, 0) := by
  rcases routeBend with
    ⟨routeIndex, incomingSegmentIndex, translate,
      incomingStart, bend, outgoingFinish⟩
  simp [RouteBend.equalityLink, RouteBend.incomingTerminal,
    RouteBend.outgoingTerminal, PeriodicEquality.normalizeLink,
    normalizeCarrierNode, Cell.sub]

/-- Two normalized bend links incident to the same terminal prototype are
identical.  The prototype endpoint determines whether it is the incoming or
outgoing side, and the indexed drawing route determines the adjacent side. -/
theorem normalizedDrawingRouteBendLink_eq_of_terminal_incident
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {first second :
      PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (firstMem :
      first ∈
        (drawingRouteBendLinks graph).map
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)))
    (secondMem :
      second ∈
        (drawingRouteBendLinks graph).map
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)))
    (firstIncident :
      first.first = .terminal indexed endpoint ∨
        first.second = .terminal indexed endpoint)
    (secondIncident :
      second.first = .terminal indexed endpoint ∨
        second.second = .terminal indexed endpoint) :
    first = second := by
  rcases List.mem_map.mp firstMem with
    ⟨firstSource, firstSourceMem, firstEq⟩
  rcases List.mem_map.mp firstSourceMem with
    ⟨firstBend, firstBendDedupMem, firstSourceEq⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondSource, secondSourceMem, secondEq⟩
  rcases List.mem_map.mp secondSourceMem with
    ⟨secondBend, secondBendDedupMem, secondSourceEq⟩
  subst first
  subst second
  subst firstSource
  subst secondSource
  have firstBendMem :
      firstBend ∈ drawingRouteBends graph :=
    List.mem_dedup.mp firstBendDedupMem
  have secondBendMem :
      secondBend ∈ drawingRouteBends graph :=
    List.mem_dedup.mp secondBendDedupMem
  cases endpoint with
  | start =>
      have firstIncident' :
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
            (firstBend.equalityLink graph)).second =
              .terminal indexed .start := by
        rcases firstIncident with firstIncident | firstIncident
        · simp at firstIncident
        · exact firstIncident
      have secondIncident' :
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
            (secondBend.equalityLink graph)).second =
              .terminal indexed .start := by
        rcases secondIncident with secondIncident | secondIncident
        · simp at secondIncident
        · exact secondIncident
      have indexedEq :
          firstBend.outgoingTerminal.indexed =
            secondBend.outgoingTerminal.indexed := by
        exact
          (PeriodicCarrierNode.terminal.inj firstIncident').1.trans
            (PeriodicCarrierNode.terminal.inj secondIncident').1.symm
      have routeEq :
          firstBend.routeIndex = secondBend.routeIndex :=
        congrArg
          (fun outgoing : IndexedGridSegment =>
            outgoing.routeIndex) indexedEq
      have successorEq :
          firstBend.incomingSegmentIndex + 1 =
            secondBend.incomingSegmentIndex + 1 :=
        congrArg
          (fun outgoing : IndexedGridSegment =>
            outgoing.segmentIndex) indexedEq
      have eraseEq :=
        drawingRouteBends_eraseTranslation_eq_of_identity_eq
          graph firstBendMem secondBendMem routeEq (by omega)
      rw [firstBend.normalize_equalityLink_eq_eraseTranslation,
        secondBend.normalize_equalityLink_eq_eraseTranslation,
        eraseEq]
  | finish =>
      have firstIncident' :
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
            (firstBend.equalityLink graph)).first =
              .terminal indexed .finish := by
        rcases firstIncident with firstIncident | firstIncident
        · exact firstIncident
        · simp at firstIncident
      have secondIncident' :
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
            (secondBend.equalityLink graph)).first =
              .terminal indexed .finish := by
        rcases secondIncident with secondIncident | secondIncident
        · exact secondIncident
        · simp at secondIncident
      have indexedEq :
          firstBend.incomingTerminal.indexed =
            secondBend.incomingTerminal.indexed := by
        exact
          (PeriodicCarrierNode.terminal.inj firstIncident').1.trans
            (PeriodicCarrierNode.terminal.inj secondIncident').1.symm
      have routeEq :
          firstBend.routeIndex = secondBend.routeIndex :=
        congrArg
          (fun incoming : IndexedGridSegment =>
            incoming.routeIndex) indexedEq
      have indexEq :
          firstBend.incomingSegmentIndex =
            secondBend.incomingSegmentIndex :=
        congrArg
          (fun incoming : IndexedGridSegment =>
            incoming.segmentIndex) indexedEq
      have eraseEq :=
        drawingRouteBends_eraseTranslation_eq_of_identity_eq
          graph firstBendMem secondBendMem routeEq indexEq
      rw [firstBend.normalize_equalityLink_eq_eraseTranslation,
        secondBend.normalize_equalityLink_eq_eraseTranslation,
        eraseEq]

/-- A normalized bend link cannot use the same terminal prototype at both
ends, because its incoming end is `finish` and its outgoing end is `start`. -/
theorem normalizedRouteBendLink_not_both_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
    {link : PeriodicEquality.NormalizedLink PeriodicCarrierNode}
    (linkMem :
      link ∈
        (drawingRouteBendLinks graph).map
          (PeriodicEquality.normalizeLink (normalizeCarrierNode graph))) :
    ¬(link.first = .terminal indexed endpoint ∧
      link.second = .terminal indexed endpoint) := by
  rcases List.mem_map.mp linkMem with
    ⟨source, sourceMem, sourceEq⟩
  rcases List.mem_map.mp sourceMem with
    ⟨routeBend, _routeBendMem, sourceLinkEq⟩
  subst link
  subst source
  intro both
  cases endpoint <;> simp_all

/-- Bend links after periodic endpoint normalization and link
deduplication. -/
def deduplicatedNormalizedRouteBendLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (PeriodicEquality.NormalizedLink PeriodicCarrierNode) :=
  ((drawingRouteBendLinks graph).map
    (PeriodicEquality.normalizeLink (normalizeCarrierNode graph))).dedup

/-- Every terminal prototype is incident to at most one normalized bend
link. -/
theorem deduplicatedNormalizedRouteBendLinks_terminal_count_le_one
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks graph)).count
        (.terminal indexed endpoint) ≤ 1 := by
  let rawLinks :=
    (drawingRouteBendLinks graph).map
      (PeriodicEquality.normalizeLink (normalizeCarrierNode graph))
  let links := rawLinks.dedup
  let target : PeriodicCarrierNode :=
    .terminal indexed endpoint
  let incidentLinks :=
    links.filter (normalizedLinkIncident target)
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  have incidentNodup : incidentLinks.Nodup :=
    linksNodup.filter _
  have incidentLengthLeOne :
      incidentLinks.length ≤ 1 := by
    cases incidentEq : incidentLinks with
    | nil =>
        simp
    | cons first rest =>
        have consNodup : (first :: rest).Nodup := by
          rw [incidentEq] at incidentNodup
          exact incidentNodup
        apply length_le_one_of_nodup_of_forall_eq
          consNodup first
        intro link linkMem
        have firstMem : first ∈ links := by
          have : first ∈ incidentLinks := by
            rw [incidentEq]
            simp
          exact (List.mem_filter.mp this).1
        have linkMem' : link ∈ links :=
          (List.mem_filter.mp (by
            show link ∈ incidentLinks
            rw [incidentEq]
            exact linkMem)).1
        have firstRaw : first ∈ rawLinks := by
          simpa [links] using firstMem
        have linkRaw : link ∈ rawLinks := by
          simpa [links] using linkMem'
        have firstIncident :
            first.first = target ∨ first.second = target :=
          (normalizedLinkIncident_eq_true_iff
            target first).mp
              (List.mem_filter.mp
                (show first ∈ incidentLinks by
                  rw [incidentEq]
                  simp)).2
        have linkIncident :
            link.first = target ∨ link.second = target :=
          (normalizedLinkIncident_eq_true_iff
            target link).mp (List.mem_filter.mp (by
              show link ∈ incidentLinks
              rw [incidentEq]
              exact linkMem)).2
        exact normalizedDrawingRouteBendLink_eq_of_terminal_incident
          graph indexed endpoint linkRaw firstRaw
            linkIncident firstIncident
  change
    (PeriodicEquality.normalizedLinkEndpoints links).count
      target ≤ 1
  rw [normalizedLinkEndpoints_count_eq_incident_length
    links target]
  · exact incidentLengthLeOne
  · intro link linkMem
    have linkRaw : link ∈ rawLinks := by
      simpa [links] using linkMem
    exact normalizedRouteBendLink_not_both_terminal
      graph indexed endpoint (by
        simpa [rawLinks] using linkRaw)

def deduplicatedNormalizedRouteBendFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    PeriodicCNF PeriodicCarrierNode :=
  PeriodicEquality.deduplicatedNormalizedFormula
    (normalizeCarrierNode graph) (drawingRouteBendLinks graph)

/-- After periodic normalization and clause deduplication, bend equalities
use a terminal prototype at most twice. -/
theorem deduplicatedNormalizedRouteBendFormula_terminal_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (deduplicatedNormalizedRouteBendFormula graph).variableOccurrences.count
      (.terminal indexed endpoint) ≤ 2 := by
  unfold deduplicatedNormalizedRouteBendFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  change
    2 * (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRouteBendLinks graph)).count
        (.terminal indexed endpoint) ≤ 2
  have endpointDegree :=
    deduplicatedNormalizedRouteBendLinks_terminal_count_le_one
      graph indexed endpoint
  omega

/-- Complete-carrier and bend equalities, each periodically normalized and
deduplicated before the two route-wire components are appended. -/
def normalizedRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    PeriodicCNF PeriodicCarrierNode :=
  ⟨(deduplicatedNormalizedCompleteCarrierFormula graph).clauses ++
    (deduplicatedNormalizedRouteBendFormula graph).clauses⟩

/-- The normalized route wire uses every terminal prototype at most eight
times: at most six occurrences from its straight carrier and at most two
from a possible bend. -/
theorem normalizedRouteWireFormula_terminal_count_le_eight
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (endpoint : SegmentEnd) :
    (normalizedRouteWireFormula graph).variableOccurrences.count
      (.terminal indexed endpoint) ≤ 8 := by
  have carrierCount :=
    deduplicatedNormalizedCompleteCarrierFormula_terminal_count_le_six
      wellFormed degree isLocal indexedMem endpoint
  have bendCount :=
    deduplicatedNormalizedRouteBendFormula_terminal_count_le_two
      graph indexed endpoint
  unfold PeriodicCNF.variableOccurrences at carrierCount bendCount
  simp only [normalizedRouteWireFormula,
    PeriodicCNF.variableOccurrences, List.flatMap_append,
    List.count_append]
  omega

end PeriodicOrthocrossing
end LeanTrominoes

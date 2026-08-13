/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Degree bounds for retained carrier representatives

The retained carrier construction selects one physical representative from
each periodic link orbit.  To bound occurrences after periodic
normalization, we first record the directed-chain uniqueness facts at both
ends of every retained carrier link.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- In a duplicate-free chain, an adjacent pair is determined by its second
entry. -/
theorem consecutivePairs_eq_of_snd_eq_of_nodup
    {Value : Type*}
    {values : List Value}
    (nodup : values.Nodup)
    {first second : Value × Value}
    (firstMem : first ∈ consecutivePairs values)
    (secondMem : second ∈ consecutivePairs values)
    (sndEq : first.2 = second.2) :
    first = second := by
  have secondEndpointsNodup :
      ((consecutivePairs values).map Prod.snd).Nodup :=
    nodup.sublist (consecutivePairs_snd_sublist values)
  exact List.inj_on_of_nodup_map secondEndpointsNodup
    firstMem secondMem sndEq

/-- A raw retained carrier link is determined by its physical second
endpoint. -/
theorem retainedDrawingCompleteCarrierLinksRaw_eq_of_second_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondEq : first.second = second.second) :
    first = second := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstKey, _firstKeyMem, firstChainMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondKey, _secondKeyMem, secondChainMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstChainMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondChainMem
  have keyEq : firstKey = secondKey := by
    rw [← firstCommon.2, ← secondCommon.2, secondEq]
  subst secondKey
  rcases List.mem_map.mp firstChainMem with
    ⟨firstPair, firstPairMem, firstLinkEq⟩
  rcases List.mem_map.mp secondChainMem with
    ⟨secondPair, secondPairMem, secondLinkEq⟩
  have pairEq :
      firstPair = secondPair := by
    apply consecutivePairs_eq_of_snd_eq_of_nodup
      (retainedCompleteCarrierNodes_nodup graph firstKey)
      (List.mem_filter.mp firstPairMem).1
      (List.mem_filter.mp secondPairMem).1
    calc
      firstPair.2 =
          first.second :=
        congrArg EqualityLink.second firstLinkEq
      _ = second.second := secondEq
      _ = secondPair.2 :=
        (congrArg EqualityLink.second secondLinkEq).symm
  subst secondPair
  exact firstLinkEq.symm.trans secondLinkEq

/-- A selected retained carrier link is determined by its physical second
endpoint. -/
theorem retainedDrawingCompleteCarrierLinks_eq_of_second_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondEq : first.second = second.second) :
    first = second := by
  exact retainedDrawingCompleteCarrierLinksRaw_eq_of_second_eq
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph first).mp firstMem).1
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph second).mp secondMem).1
    secondEq

/-- Translating a selected link so that its second endpoint is canonical
keeps it inside the raw retained window. -/
theorem
    retainedDrawingCompleteCarrierLink_secondNormalize_mem_raw
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    carrierLinkPeriodTranslate graph link
        (Cell.neg (normalizeCarrierNode graph link.second).2) ∈
      retainedDrawingCompleteCarrierLinksRaw graph := by
  have rawMem :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have common :=
    retainedDrawingCompleteCarrierLinks_common_key graph linkMem
  have fields :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph endpoints.1)
      (retainedCarrierNode_indexed_mem graph endpoints.2)
      common
  apply retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    wellFormed degree isLocal rawMem
  · exact
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph linkMem
  · have targetTranslateEq :
        (link.first.periodTranslate graph
            (Cell.neg
              (normalizeCarrierNode graph link.second).2)).translate =
          (link.second.periodTranslate graph
            (Cell.neg
              (normalizeCarrierNode graph link.second).2)).translate := by
      simp only [CarrierNode.translate_periodTranslate]
      rw [fields.2]
    rw [targetTranslateEq]
    cases secondEq : link.second with
    | terminal terminal =>
        rcases terminal with ⟨indexed, translate, endpoint⟩
        simp [normalizeCarrierNode,
          CarrierNode.periodTranslate,
          SegmentTerminal.periodTranslate,
          CarrierNode.translate,
          Cell.neg, Cell.sub, Cell.add,
          IsNeighborTranslation]
    | boundary boundary =>
        have boundaryMem :
            boundary ∈ retainedCrossingBoundaries graph := by
          rw [secondEq] at endpoints
          unfold retainedDrawingCarrierNodes at endpoints
          simpa using endpoints.2
        have normalizedMem :
            boundary.periodNormalize graph ∈
              drawingCrossingBoundaries graph :=
          retainedCrossingBoundary_periodNormalize_mem
            graph boundaryMem
        have normalizedNeighbor :=
          (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
            graph normalizedMem).2
        simpa [normalizeCarrierNode,
          CarrierNode.periodTranslate,
          CarrierNode.translate,
          CrossingBoundary.periodTranslate,
          CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize,
          CrossingBoundary.periodNormalize] using normalizedNeighbor

/-- After periodic normalization, a retained link is still determined by
its second endpoint prototype. -/
theorem retainedDrawingCompleteCarrierLinks_normalizeLink_eq_of_second_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (normalizedSecondEq :
      (normalizeCarrierNode graph first.second).1 =
        (normalizeCarrierNode graph second.second).1) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph) first =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        second := by
  let firstCanonical :=
    carrierLinkPeriodTranslate graph first
      (Cell.neg (normalizeCarrierNode graph first.second).2)
  let secondCanonical :=
    carrierLinkPeriodTranslate graph second
      (Cell.neg (normalizeCarrierNode graph second.second).2)
  have firstCanonicalMem :
      firstCanonical ∈
        retainedDrawingCompleteCarrierLinksRaw graph :=
    retainedDrawingCompleteCarrierLink_secondNormalize_mem_raw
      wellFormed degree isLocal firstMem
  have secondCanonicalMem :
      secondCanonical ∈
        retainedDrawingCompleteCarrierLinksRaw graph :=
    retainedDrawingCompleteCarrierLink_secondNormalize_mem_raw
      wellFormed degree isLocal secondMem
  have canonicalSecondEq :
      firstCanonical.second = secondCanonical.second := by
    cases firstNode : first.second with
    | terminal firstTerminal =>
        cases secondNode : second.second with
        | boundary secondBoundary =>
            simp [firstNode, secondNode, normalizeCarrierNode]
              at normalizedSecondEq
        | terminal secondTerminal =>
            have terminalData :
                firstTerminal.indexed = secondTerminal.indexed ∧
                  firstTerminal.endpoint = secondTerminal.endpoint := by
              simpa [firstNode, secondNode, normalizeCarrierNode] using
                normalizedSecondEq
            rcases firstTerminal with
              ⟨firstIndexed, firstTranslate, firstEndpoint⟩
            rcases secondTerminal with
              ⟨secondIndexed, secondTranslate, secondEndpoint⟩
            rcases firstTranslate with ⟨firstX, firstY⟩
            rcases secondTranslate with ⟨secondX, secondY⟩
            simp only at terminalData
            simp [firstCanonical, secondCanonical,
              carrierLinkPeriodTranslate,
              firstNode, secondNode, normalizeCarrierNode,
              CarrierNode.periodTranslate,
              SegmentTerminal.periodTranslate,
              Cell.neg, Cell.sub, Cell.add,
              terminalData.1, terminalData.2]
    | boundary firstBoundary =>
        cases secondNode : second.second with
        | terminal secondTerminal =>
            simp [firstNode, secondNode, normalizeCarrierNode]
              at normalizedSecondEq
        | boundary secondBoundary =>
            have boundaryEq :
                firstBoundary.periodNormalize graph =
                  secondBoundary.periodNormalize graph := by
              simpa [firstNode, secondNode, normalizeCarrierNode] using
                normalizedSecondEq
            have firstCanonicalSecond :
                firstCanonical.second =
                  .boundary
                    (firstBoundary.periodNormalize graph) := by
              simp [firstCanonical, carrierLinkPeriodTranslate,
                firstNode, normalizeCarrierNode,
                CarrierNode.periodTranslate,
                CrossingBoundary.periodTranslate,
                CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize,
                CrossingBoundary.periodNormalize]
            have secondCanonicalSecond :
                secondCanonical.second =
                  .boundary
                    (secondBoundary.periodNormalize graph) := by
              simp [secondCanonical, carrierLinkPeriodTranslate,
                secondNode, normalizeCarrierNode,
                CarrierNode.periodTranslate,
                CrossingBoundary.periodTranslate,
                CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize,
                CrossingBoundary.periodNormalize]
            rw [firstCanonicalSecond, secondCanonicalSecond, boundaryEq]
  have canonicalEq : firstCanonical = secondCanonical :=
    retainedDrawingCompleteCarrierLinksRaw_eq_of_second_eq
      firstCanonicalMem secondCanonicalMem canonicalSecondEq
  calc
    PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph) first =
      PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph) firstCanonical := by
          symm
          exact normalizeLink_carrierLinkPeriodTranslate
            graph first
              (Cell.neg
                (normalizeCarrierNode graph first.second).2)
    _ =
      PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph) secondCanonical := by
          rw [canonicalEq]
    _ =
      PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph) second :=
          normalizeLink_carrierLinkPeriodTranslate
            graph second
              (Cell.neg
                (normalizeCarrierNode graph second.second).2)

/-- The normalized retained-link representatives after link-level
deduplication. -/
def deduplicatedNormalizedRetainedCompleteCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (PeriodicEquality.NormalizedLink PeriodicCarrierNode) :=
  ((retainedDrawingCompleteCarrierLinks graph).map
    (PeriodicEquality.normalizeLink
      (normalizeCarrierNode graph))).dedup

/-- Normalized retained links have pairwise-distinct first endpoints. -/
theorem
    deduplicatedNormalizedRetainedCompleteCarrierLinks_first_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ((deduplicatedNormalizedRetainedCompleteCarrierLinks graph).map
      PeriodicEquality.NormalizedLink.first).Nodup := by
  let rawLinks :=
    (retainedDrawingCompleteCarrierLinks graph).map
      (PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph))
  let links := rawLinks.dedup
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  change
    (links.map
      PeriodicEquality.NormalizedLink.first).Nodup
  apply linksNodup.map_on
  intro first firstMem second secondMem firstEq
  have firstRaw : first ∈ rawLinks := by
    simpa [links] using firstMem
  have secondRaw : second ∈ rawLinks := by
    simpa [links] using secondMem
  rcases List.mem_map.mp firstRaw with
    ⟨firstSource, firstSourceMem, firstSourceEq⟩
  rcases List.mem_map.mp secondRaw with
    ⟨secondSource, secondSourceMem, secondSourceEq⟩
  subst first
  subst second
  exact
    retainedDrawingCompleteCarrierLinks_normalizeLink_eq_of_first_eq
      wellFormed degree isLocal
      firstSourceMem secondSourceMem firstEq

/-- Normalized retained links have pairwise-distinct second endpoints. -/
theorem
    deduplicatedNormalizedRetainedCompleteCarrierLinks_second_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ((deduplicatedNormalizedRetainedCompleteCarrierLinks graph).map
      PeriodicEquality.NormalizedLink.second).Nodup := by
  let rawLinks :=
    (retainedDrawingCompleteCarrierLinks graph).map
      (PeriodicEquality.normalizeLink
        (normalizeCarrierNode graph))
  let links := rawLinks.dedup
  have linksNodup : links.Nodup :=
    List.nodup_dedup rawLinks
  change
    (links.map
      PeriodicEquality.NormalizedLink.second).Nodup
  apply linksNodup.map_on
  intro first firstMem second secondMem secondEq
  have firstRaw : first ∈ rawLinks := by
    simpa [links] using firstMem
  have secondRaw : second ∈ rawLinks := by
    simpa [links] using secondMem
  rcases List.mem_map.mp firstRaw with
    ⟨firstSource, firstSourceMem, firstSourceEq⟩
  rcases List.mem_map.mp secondRaw with
    ⟨secondSource, secondSourceMem, secondSourceEq⟩
  subst first
  subst second
  exact
    retainedDrawingCompleteCarrierLinks_normalizeLink_eq_of_second_eq
      wellFormed degree isLocal
      firstSourceMem secondSourceMem secondEq

/-- Endpoint multiplicity splits into the first- and second-endpoint
multiplicities. -/
theorem normalizedLinkEndpoints_count_eq_first_add_second
    {Variable : Type*} [DecidableEq Variable]
    (links : List (PeriodicEquality.NormalizedLink Variable))
    (target : Variable) :
    (PeriodicEquality.normalizedLinkEndpoints links).count target =
      (links.map
        PeriodicEquality.NormalizedLink.first).count target +
      (links.map
        PeriodicEquality.NormalizedLink.second).count target := by
  unfold PeriodicEquality.normalizedLinkEndpoints
  induction links with
  | nil =>
      simp
  | cons link links induction =>
      rcases link with ⟨first, second, offset⟩
      by_cases firstEq : first = target <;>
        by_cases secondEq : second = target <;>
          simp [firstEq, secondEq, induction] <;> omega

/-- Every normalized retained carrier prototype is incident to at most two
retained link representatives: one predecessor and one successor. -/
theorem
    deduplicatedNormalizedRetainedCompleteCarrierLinks_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (target : PeriodicCarrierNode) :
    (PeriodicEquality.normalizedLinkEndpoints
      (deduplicatedNormalizedRetainedCompleteCarrierLinks graph)).count
        target ≤ 2 := by
  rw [normalizedLinkEndpoints_count_eq_first_add_second]
  have firstLe :
      ((deduplicatedNormalizedRetainedCompleteCarrierLinks graph).map
        PeriodicEquality.NormalizedLink.first).count target ≤ 1 :=
    (List.nodup_iff_count_le_one.mp
      (deduplicatedNormalizedRetainedCompleteCarrierLinks_first_nodup
        wellFormed degree isLocal)) target
  have secondLe :
      ((deduplicatedNormalizedRetainedCompleteCarrierLinks graph).map
        PeriodicEquality.NormalizedLink.second).count target ≤ 1 :=
    (List.nodup_iff_count_le_one.mp
      (deduplicatedNormalizedRetainedCompleteCarrierLinks_second_nodup
        wellFormed degree isLocal)) target
  omega

/-- The periodically normalized retained straight-carrier equality
formula. -/
def deduplicatedNormalizedRetainedCompleteCarrierFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    PeriodicCNF PeriodicCarrierNode :=
  PeriodicEquality.deduplicatedNormalizedFormula
    (normalizeCarrierNode graph)
    (retainedDrawingCompleteCarrierLinks graph)

/-- Every prototype occurs at most four times in the normalized retained
straight-carrier equality formula. -/
theorem
    deduplicatedNormalizedRetainedCompleteCarrierFormula_occurrencesAtMostFour
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    (deduplicatedNormalizedRetainedCompleteCarrierFormula
      graph).OccurrencesAtMost 4 := by
  apply
    PeriodicEquality.deduplicatedNormalizedFormula_occurrencesAtMost
      (normalizeCarrierNode graph)
      (retainedDrawingCompleteCarrierLinks graph)
      2 4 rfl
  exact
    deduplicatedNormalizedRetainedCompleteCarrierLinks_count_le_two
      wellFormed degree isLocal

end PeriodicOrthocrossing
end LeanTrominoes

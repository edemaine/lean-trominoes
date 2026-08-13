/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership

/-!
# Representative carrier links through retained crossings

This file builds the candidate periodic carrier family promised by
`PeriodicOrthocrossingCarrierOrbitOwnership`.  Every halo crossing contributes
physical split points to the sorted finite carrier chains.  We first enumerate
all links visible in the retained window, then keep only the zero-shift owner
of each prospective periodic link.

The old canonical carrier family remains unchanged while this replacement is
verified.  The definitions here are therefore intentionally parallel to the
ones in `PeriodicOrthocrossingPlanarTerminals`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- All retained segment terminals and halo crossing boundaries before
grouping by physical carrier key. -/
def retainedDrawingCarrierNodes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CarrierNode :=
  (drawingSegmentTerminals graph).map CarrierNode.terminal ++
    (retainedCrossingBoundaries graph).map CarrierNode.boundary

/-- All retained nodes on one physical segment occurrence, sorted along its
axis. -/
def retainedCompleteCarrierNodes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List CarrierNode :=
  ((retainedDrawingCarrierNodes graph).dedup.filter fun node =>
    node.carrierKey = key).insertionSort fun first second =>
      first.orderCoordinate graph ≤ second.orderCoordinate graph

@[simp]
theorem mem_retainedCompleteCarrierNodes_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) (node : CarrierNode) :
    node ∈ retainedCompleteCarrierNodes graph key ↔
      node ∈ retainedDrawingCarrierNodes graph ∧
        node.carrierKey = key := by
  simp [retainedCompleteCarrierNodes]

/-- Deduplication before sorting makes every retained carrier chain a simple
node list. -/
theorem retainedCompleteCarrierNodes_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) :
    (retainedCompleteCarrierNodes graph key).Nodup := by
  unfold retainedCompleteCarrierNodes
  apply
    (List.perm_insertionSort
      (fun first second =>
        first.orderCoordinate graph ≤
          second.orderCoordinate graph)
      ((retainedDrawingCarrierNodes graph).dedup.filter fun node =>
        node.carrierKey = key)).nodup_iff.mpr
  exact (List.nodup_dedup _).filter _

/-- The raw equality chain on one retained physical carrier. -/
def retainedCompleteCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List (EqualityLink CarrierNode) :=
  ((consecutivePairs
      (retainedCompleteCarrierNodes graph key)).filter fun pair =>
    !pair.1.sameCrossoverSite pair.2).map
      (carrierNodePairLink graph)

/-- Every retained link stays on its requested physical carrier key. -/
theorem retainedCompleteCarrierLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedCompleteCarrierLinks graph key) :
    link.first.carrierKey = key ∧
      link.second.carrierKey = key := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have rawPairMem := (List.mem_filter.mp pairMem).1
  have members := mem_of_mem_consecutivePairs rawPairMem
  exact
    ⟨(mem_retainedCompleteCarrierNodes_iff
        graph key pair.1).mp members.1 |>.2,
      (mem_retainedCompleteCarrierNodes_iff
        graph key pair.2).mp members.2 |>.2⟩

/-- Every physical carrier key represented in the retained window. -/
def retainedDrawingCompleteCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  ((retainedDrawingCarrierNodes graph).map
    CarrierNode.carrierKey).dedup

/-- All raw complete-carrier links visible in the retained halo window. -/
def retainedDrawingCompleteCarrierLinksRaw
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CarrierNode) :=
  (retainedDrawingCompleteCarrierKeys graph).flatMap fun key =>
    retainedCompleteCarrierLinks graph key

/-- Every raw retained link stays on one physical carrier. -/
theorem retainedDrawingCompleteCarrierLinksRaw_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈
      retainedDrawingCompleteCarrierLinksRaw graph) :
    link.first.carrierKey = link.second.carrierKey := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  have common :=
    retainedCompleteCarrierLinks_common_key graph key linkMem
  exact common.1.trans common.2.symm

/-- One zero-shift representative of every prospective periodic carrier link
visible in the retained window. -/
def retainedDrawingCompleteCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CarrierNode) :=
  (retainedDrawingCompleteCarrierLinksRaw graph).filter
    (CarrierLinkIsRepresentative graph)

@[simp]
theorem mem_retainedDrawingCompleteCarrierLinks_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) :
    link ∈ retainedDrawingCompleteCarrierLinks graph ↔
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph ∧
        CarrierLinkIsRepresentative graph link := by
  simp [retainedDrawingCompleteCarrierLinks]

/-- Every selected retained link stays on one physical carrier. -/
theorem retainedDrawingCompleteCarrierLinks_common_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    link.first.carrierKey = link.second.carrierKey := by
  exact retainedDrawingCompleteCarrierLinksRaw_common_key graph
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1

/-- Both endpoints of a raw retained link are listed retained carrier nodes. -/
theorem retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    link.first ∈ retainedDrawingCarrierNodes graph ∧
      link.second ∈ retainedDrawingCarrierNodes graph := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have rawPairMem := (List.mem_filter.mp pairMem).1
  have members := mem_of_mem_consecutivePairs rawPairMem
  exact
    ⟨(mem_retainedCompleteCarrierNodes_iff
        graph key pair.1).mp members.1 |>.1,
      (mem_retainedCompleteCarrierNodes_iff
        graph key pair.2).mp members.2 |>.1⟩

/-- Both endpoints of a selected representative link are retained carrier
nodes. -/
theorem retainedDrawingCompleteCarrierLink_endpoints_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph) :
    link.first ∈ retainedDrawingCarrierNodes graph ∧
      link.second ∈ retainedDrawingCarrierNodes graph := by
  exact retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1

/-- Adjacent pairs of a duplicate-free list are duplicate-free. -/
theorem retained_consecutivePairs_nodup_of_nodup
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (nodup : values.Nodup) :
    (consecutivePairs values).Nodup := by
  induction values with
  | nil =>
      simp [consecutivePairs]
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [consecutivePairs]
      | cons second tail =>
          have firstNotMem : first ∉ second :: tail :=
            (List.nodup_cons.mp nodup).1
          have restNodup : (second :: tail).Nodup :=
            (List.nodup_cons.mp nodup).2
          rw [consecutivePairs]
          apply List.Nodup.cons
          · intro pairMem
            have members :=
              mem_of_mem_consecutivePairs pairMem
            exact firstNotMem (by simp [members.1])
          · exact induction restNodup

/-- Each raw retained carrier chain contains no repeated equality link. -/
theorem retainedCompleteCarrierLinks_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) :
    (retainedCompleteCarrierLinks graph key).Nodup := by
  have pairsNodup :
      (consecutivePairs
        (retainedCompleteCarrierNodes graph key)).Nodup :=
    retained_consecutivePairs_nodup_of_nodup _
      (retainedCompleteCarrierNodes_nodup graph key)
  have filteredNodup :=
    pairsNodup.filter fun pair =>
      !pair.1.sameCrossoverSite pair.2
  apply filteredNodup.map
  intro first second equal
  exact Prod.ext
    (congrArg EqualityLink.first equal)
    (congrArg EqualityLink.second equal)

/-- Raw retained links from different carrier keys are disjoint. -/
theorem retainedCompleteCarrierLinks_disjoint_of_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {firstKey secondKey : Nat × Nat × Cell}
    (different : firstKey ≠ secondKey) :
    List.Disjoint
      (retainedCompleteCarrierLinks graph firstKey)
      (retainedCompleteCarrierLinks graph secondKey) := by
  rw [List.disjoint_left]
  intro link firstMember secondMember
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstMember
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondMember
  exact different (firstCommon.1.symm.trans secondCommon.1)

/-- The complete raw retained carrier family has no duplicate physical
links. -/
theorem retainedDrawingCompleteCarrierLinksRaw_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (retainedDrawingCompleteCarrierLinksRaw graph).Nodup := by
  rw [retainedDrawingCompleteCarrierLinksRaw, List.nodup_flatMap]
  constructor
  · intro key _keyMember
    exact retainedCompleteCarrierLinks_nodup graph key
  · exact
      (List.nodup_iff_pairwise_ne.mp
        (List.nodup_dedup
          ((retainedDrawingCarrierNodes graph).map
            CarrierNode.carrierKey))).imp fun
        {firstKey secondKey} different =>
          retainedCompleteCarrierLinks_disjoint_of_ne
            graph different

/-- Filtering by periodic ownership preserves physical-link
duplicate-freedom. -/
theorem retainedDrawingCompleteCarrierLinks_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (retainedDrawingCompleteCarrierLinks graph).Nodup := by
  exact
    (retainedDrawingCompleteCarrierLinksRaw_nodup graph).filter _

/-- Positioned equality clauses for the selected retained carrier
representatives. -/
def retainedDrawingCompleteCarrierFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CarrierNode) :=
  equalityFamily (retainedDrawingCompleteCarrierLinks graph)

/-- Any segment-occurrence assignment satisfies every retained representative
carrier link. -/
theorem retainedDrawingCompleteCarrierFormula_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : (Nat × Nat × Cell) → Bool) :
    FormulaHolds (assignment ∘ CarrierNode.carrierKey)
      (retainedDrawingCompleteCarrierFormula graph) := by
  apply equalityFamily_holds_of_common_key
    CarrierNode.carrierKey assignment
      (retainedDrawingCompleteCarrierLinks graph)
  intro link linkMem
  exact retainedDrawingCompleteCarrierLinks_common_key graph linkMem

end PeriodicOrthocrossing
end LeanTrominoes

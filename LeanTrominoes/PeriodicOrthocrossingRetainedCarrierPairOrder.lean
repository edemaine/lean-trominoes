import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBoundingBox

/-!
# Pair order on selected retained carriers

Nodes with one retained occurrence key have a common axis tag.  Distinct
selected links drawn from that key's strictly sorted consecutive-pair chain
therefore have one of the two nonoverlapping axial orders.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Retained nodes on one physical carrier have the same axis tag. -/
theorem retainedCarrierNode_isHorizontal_iff_of_commonCarrier
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    first.isHorizontal = true ↔
      second.isHorizontal = true := by
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstMem)
      (retainedCarrierNode_indexed_mem graph secondMem)
      keyEqual
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      first.indexed
      (retainedCarrierNode_indexed_mem graph firstMem)
  have secondAligned :
      second.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  constructor
  · intro firstHorizontalTag
    have firstHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph firstMem firstAligned).mp firstHorizontalTag
    have secondHorizontal :
        second.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    exact
      (retainedCarrierNode_isHorizontal_iff
        graph secondMem secondAligned).mpr secondHorizontal
  · intro secondHorizontalTag
    have secondHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph secondMem secondAligned).mp secondHorizontalTag
    have firstHorizontal :
        first.indexed.segment.IsHorizontal := by
      rw [occurrenceEqual.1]
      exact secondHorizontal
    exact
      (retainedCarrierNode_isHorizontal_iff
        graph firstMem firstAligned).mpr firstHorizontal

/-- Distinct selected retained links with the same carrier key occur in one
of the two nonoverlapping axial orders. -/
theorem retainedDrawingCompleteCarrierLinks_same_key_orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (different : firstLink ≠ secondLink)
    (sameKey :
      firstLink.first.carrierKey =
        secondLink.first.carrierKey) :
    firstLink.second.orderCoordinate graph ≤
        secondLink.first.orderCoordinate graph ∨
      secondLink.second.orderCoordinate graph ≤
        firstLink.first.orderCoordinate graph := by
  have firstRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph firstLink).mp firstMem).1
  have secondRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph secondLink).mp secondMem).1
  rcases List.mem_flatMap.mp firstRaw with
    ⟨firstKey, _firstKeyMem, firstLinkMem⟩
  rcases List.mem_flatMap.mp secondRaw with
    ⟨secondKey, _secondKeyMem, secondLinkMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstLinkMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondLinkMem
  have keyEqual : firstKey = secondKey :=
    firstCommon.1.symm.trans
      (sameKey.trans secondCommon.1)
  subst secondKey
  rcases List.mem_map.mp firstLinkMem with
    ⟨firstPair, firstPairMem, firstLinkEqual⟩
  rcases List.mem_map.mp secondLinkMem with
    ⟨secondPair, secondPairMem, secondLinkEqual⟩
  subst firstLink
  subst secondLink
  have firstPairRaw :=
    (List.mem_filter.mp firstPairMem).1
  have secondPairRaw :=
    (List.mem_filter.mp secondPairMem).1
  have pairDifferent : firstPair ≠ secondPair := by
    intro pairEqual
    subst secondPair
    exact different rfl
  simpa [carrierNodePairLink] using
    List.consecutivePairs_nonoverlap_of_ne_of_pairwise_lt
      (CarrierNode.orderCoordinate graph)
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal firstKey)
      firstPairRaw secondPairRaw pairDifferent

end PeriodicOrthocrossing
end LeanTrominoes

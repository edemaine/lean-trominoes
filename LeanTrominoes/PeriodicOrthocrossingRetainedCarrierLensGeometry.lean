import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierGeometry

/-!
# Equality-lens geometry for retained carrier links

Strict retained-chain order and the common `1 mod 10` residue give every
adjacent pair at least ten refined cells of forward separation.  Thus the
existing generic equality-lens construction applies unchanged to both raw
retained links and their selected zero-shift representatives.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every adjacent retained carrier pair has enough physical clearance for
the eight-cell equality lens. -/
theorem retainedCompleteCarrierPair_hasForwardClearance
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {pair : CarrierNode × CarrierNode}
    (pairMem :
      pair ∈ consecutivePairs
        (retainedCompleteCarrierNodes graph key)) :
    pair.1.HasForwardClearance graph pair.2 := by
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.1).mp members.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.2).mp members.2
  have keyEqual :
      pair.1.carrierKey = pair.2.carrierKey :=
    firstData.2.trans secondData.2.symm
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstData.1)
      (retainedCarrierNode_indexed_mem graph secondData.1)
      keyEqual
  have firstAligned :
      pair.1.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      pair.1.indexed
      (retainedCarrierNode_indexed_mem graph firstData.1)
  have secondAligned :
      pair.2.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  have axisData :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal
      firstData.1 secondData.1 keyEqual
  have strict :=
    consecutivePairs_rel_of_pairwise
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal key)
      pairMem
  unfold CarrierNode.HasForwardClearance
  by_cases horizontal : pair.1.isHorizontal = true
  · rw [if_pos horizontal]
    have firstHorizontal :
        pair.1.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph firstData.1 firstAligned).mp horizontal
    have secondHorizontal :
        pair.2.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    have secondHorizontalTag :
        pair.2.isHorizontal = true :=
      (retainedCarrierNode_isHorizontal_iff
        graph secondData.1 secondAligned).mpr secondHorizontal
    have axisData' :
        (pair.1.position graph).2 =
            (pair.2.position graph).2 ∧
          (pair.1.position graph).1 % 10 = 1 ∧
          (pair.2.position graph).1 % 10 = 1 := by
      simpa [horizontal] using axisData
    have strict' :
        (pair.1.position graph).1 <
          (pair.2.position graph).1 := by
      simpa [CarrierNode.orderCoordinate,
        horizontal, secondHorizontalTag] using strict
    omega
  · rw [if_neg horizontal]
    have secondNotHorizontalTag :
        ¬pair.2.isHorizontal = true := by
      intro secondHorizontalTag
      have secondHorizontal :=
        (retainedCarrierNode_isHorizontal_iff
          graph secondData.1 secondAligned).mp secondHorizontalTag
      have firstHorizontal :
          pair.1.indexed.segment.IsHorizontal := by
        rw [occurrenceEqual.1]
        exact secondHorizontal
      exact horizontal
        ((retainedCarrierNode_isHorizontal_iff
          graph firstData.1 firstAligned).mpr firstHorizontal)
    have axisData' :
        (pair.1.position graph).1 =
            (pair.2.position graph).1 ∧
          (pair.1.position graph).2 % 10 = 1 ∧
          (pair.2.position graph).2 % 10 = 1 := by
      simpa [horizontal] using axisData
    have strict' :
        (pair.1.position graph).2 <
          (pair.2.position graph).2 := by
      simpa [CarrierNode.orderCoordinate,
        horizontal, secondNotHorizontalTag] using strict
    omega

/-- Every raw equality link in one retained carrier chain satisfies the
generic equality-lens geometry interface. -/
theorem retainedCompleteCarrierLink_lensGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedCompleteCarrierLinks graph key) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph) link := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  apply
    carrierNodePairLink_lensGeometry_of_hasForwardClearance
      graph pair
  · exact consecutivePairs_ne_of_nodup
      (retainedCompleteCarrierNodes_nodup graph key) pairData.1
  · exact retainedCompleteCarrierPair_hasForwardClearance
      wellFormed degree isLocal key pairData.1

/-- Every raw retained carrier link inherits certified lens geometry. -/
theorem retainedDrawingCompleteCarrierLinkRaw_lensGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph) link := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  exact retainedCompleteCarrierLink_lensGeometry
    wellFormed degree isLocal key linkMem

/-- Every selected zero-shift carrier representative inherits certified lens
geometry. -/
theorem retainedDrawingCompleteCarrierLink_lensGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph) link :=
  retainedDrawingCompleteCarrierLinkRaw_lensGeometry
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1

/-- Each selected retained lens draws exactly its source equality instance. -/
theorem retainedDrawingCompleteCarrierLink_lensDrawing_formula
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).formula =
        equalityInstance link.first link.second link.positions :=
  EqualityLink.lensDrawing_formula
    (retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Each selected retained lens recovers its first endpoint position. -/
theorem retainedDrawingCompleteCarrierLink_lensDrawing_firstPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).variablePosition link.first =
        link.first.position graph :=
  EqualityLink.lensDrawing_firstPosition
    (retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Each selected retained lens recovers its second endpoint position. -/
theorem retainedDrawingCompleteCarrierLink_lensDrawing_secondPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).variablePosition link.second =
        link.second.position graph :=
  EqualityLink.lensDrawing_secondPosition
    (retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Every selected retained lens has exact endpoints, orthogonal routes, and
continuous finite planarity. -/
theorem retainedDrawingCompleteCarrierLink_lensDrawing_isValid
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).IsValid :=
  EqualityLink.lensDrawing_isValid
    (retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

end PeriodicOrthocrossing
end LeanTrominoes

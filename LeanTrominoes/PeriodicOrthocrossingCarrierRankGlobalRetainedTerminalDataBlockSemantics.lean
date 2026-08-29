/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalRetainedCompactWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairGlobalSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-! # Physical semantics of retained carrier terminal-data blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

namespace CarrierRankGlobal

/-- Filtering one deduplicated rank block and projecting its terminal data
is exactly the same projection of its representative physical node pairs. -/
theorem dedupKeyBlockRetainedTerminalDataBlocks_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    ((((keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            carrierLensRouteTerminalDataBlock pair.1.horizontal
              (pair.2.orderCoordinate - pair.1.orderCoordinate)) =
      (retainedRepresentativeCarrierNodePairsAtPeriod
        period nodes key).map fun pair =>
          carrierLensRouteTerminalDataBlock pair.1.isHorizontal
            (carrierNodeOrderCoordinateAtPeriod period pair.2 -
              carrierNodeOrderCoordinateAtPeriod period pair.1) := by
  dsimp only
  rw [dedupKeyBlockDatumPairs_eq_physicalPairs period nodes key]
  unfold retainedRepresentativeCarrierNodePairsAtPeriod
    retainedCompleteCarrierNodePairsAtPeriod
  rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
  simp only [List.filter_map, List.map_map, Function.comp_def,
    carrierNodeRankDatumAtPeriod_sameCrossoverSite,
    carrierNodeRankDatumAtPeriod_pairIsRepresentative]
  apply List.map_congr_left
  intro pair _pairMember
  simp [carrierNodeRankDatumAtPeriod,
    carrierNodeOrderCoordinateAtPeriod]

/-- The preceding block equality concatenates over every stable carrier key
without changing presentation order. -/
theorem dedupGlobalRetainedTerminalDataBlocks_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let keys := (datums.map CarrierNodeRankDatum.key).dedup
    keys.flatMap (fun key =>
      ((((keyBlockDatumPairs datums key).filter fun pair =>
          !pair.1.sameCrossoverSite pair.2).filter fun pair =>
            pair.1.pairIsRepresentative pair.2).map fun pair =>
              carrierLensRouteTerminalDataBlock pair.1.horizontal
                (pair.2.orderCoordinate - pair.1.orderCoordinate))) =
      keys.flatMap fun key =>
        (retainedRepresentativeCarrierNodePairsAtPeriod
          period nodes key).map fun pair =>
            carrierLensRouteTerminalDataBlock pair.1.isHorizontal
              (carrierNodeOrderCoordinateAtPeriod period pair.2 -
                carrierNodeOrderCoordinateAtPeriod period pair.1) := by
  dsimp only
  apply List.flatMap_congr
  intro key _keyMember
  exact dedupKeyBlockRetainedTerminalDataBlocks_eq_physicalPairs
    period nodes key

end CarrierRankGlobal

/-- At the drawing period, the physical node-pair terminal blocks are the
terminal blocks of the corresponding semantic retained links. -/
theorem retainedRepresentativeCarrierNodeTerminalDataBlocks_eq_links
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell) :
    ((retainedRepresentativeCarrierNodePairsAtPeriod
        (drawingGridSize graph)
        (retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
          (drawingGridSize graph)
          (neighborOccurrences graph)
          (orientedCrossingOccurrencePairs graph)) key).map fun pair =>
      carrierLensRouteTerminalDataBlock pair.1.isHorizontal
        (carrierNodeOrderCoordinateAtPeriod
            (drawingGridSize graph) pair.2 -
          carrierNodeOrderCoordinateAtPeriod
            (drawingGridSize graph) pair.1)) =
      ((retainedRepresentativeCarrierLinksAt graph key).map fun link =>
        carrierLensRouteTerminalDataBlock link.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position graph link.first)
            (CarrierNode.position graph link.second))) := by
  rw [retainedRepresentativeCarrierLinksAt_eq_nodePairsAtPeriod]
  rw [List.map_map]
  apply List.map_congr_left
  intro pair pairMember
  have rawPairMember := (List.mem_filter.mp pairMember).1
  have consecutiveMember :
      pair ∈ consecutivePairs (retainedCompleteCarrierNodes graph key) := by
    unfold retainedCompleteCarrierNodePairsAtPeriod at rawPairMember
    have consecutiveAtPeriod := (List.mem_filter.mp rawPairMember).1
    rw [← retainedCompleteCarrierNodes_eq_occurrencesAndPairsAtPeriod]
      at consecutiveAtPeriod
    exact consecutiveAtPeriod
  have members := mem_of_mem_consecutivePairs consecutiveMember
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff graph key pair.1).mp members.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff graph key pair.2).mp members.2
  have sameAxis : pair.1.isHorizontal = pair.2.isHorizontal :=
    retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
      wellFormed degree isLocal firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)
  have clearance := retainedCompleteCarrierPair_hasForwardClearance
    wellFormed degree isLocal key consecutiveMember
  have spanEq :=
    CarrierNode.axisSpan_eq_orderCoordinate_sub_of_hasForwardClearance
      graph pair.1 pair.2 sameAxis clearance
  simp only [Function.comp_apply, carrierNodePairLink,
    carrierNodeOrderCoordinateAtPeriod_drawingGridSize]
  rw [spanEq]

end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapDedup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkBitData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkBitKeySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDescriptorBitSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairKeyBlockNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyBlockSemantics

/-! # Exact retained carrier-link semantics of the rank-ordered compiler -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem routeDescriptorRetainedCarrierNodes_numeric_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    routeDescriptorRetainedCarrierNodesAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) =
      retainedDrawingCarrierNodes formula.incidenceGraph := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  unfold routeDescriptorRetainedCarrierNodesAtPeriod
  rw [incidenceGraph_neighborOccurrences_eq_numeric,
    numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences,
    incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric,
    numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]

theorem dedupDatumKeys_numeric_eq_completeKeys
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    let descriptors := numericRouteDescriptors formula
    let period := routeDescriptorStreamGridSize descriptors
    let sourceDatums :=
      routeDescriptorCarrierRankDatumsAtPeriod period descriptors
    let datums := sourceDatums.dedup
    (datums.map CarrierNodeRankDatum.key).dedup =
      retainedDrawingCompleteCarrierKeys formula.incidenceGraph := by
  let descriptors := numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let sourceDatums :=
    routeDescriptorCarrierRankDatumsAtPeriod period descriptors
  let datums := sourceDatums.dedup
  change (datums.map CarrierNodeRankDatum.key).dedup = _
  rw [show datums = sourceDatums.dedup by rfl]
  rw [List.dedup_map_dedup]
  unfold sourceDatums routeDescriptorCarrierRankDatumsAtPeriod
  rw [List.map_map]
  change ((routeDescriptorRetainedCarrierNodesAtPeriod
      period descriptors).map CarrierNode.carrierKey).dedup = _
  have periodEq : period = drawingGridSize formula.incidenceGraph := by
    simpa [period, descriptors] using
      routeDescriptorStreamGridSize_numericRouteDescriptors
        formula nonempty
  rw [periodEq]
  rw [routeDescriptorRetainedCarrierNodes_numeric_eq formula]
  rfl

/-- Under the route invariants used by Theorem 5.2, the compiled sparse bit
stream is exactly the semantic presentation-order retained carrier-link bit
stream. -/
theorem retainedPairBits_numericRouteDescriptors_eq_retainedCarrierLinkBits
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    CarrierRankOrderedPairs.retainedPairBits
        (numericRouteDescriptors formula) =
      retainedCarrierLinkBits formula.incidenceGraph
        (carrierLinkNextSlice formula) := by
  let descriptors := numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let sourceDatums :=
    routeDescriptorCarrierRankDatumsAtPeriod period descriptors
  let datums := sourceDatums.dedup
  rw [CarrierRankOrderedPairs.retainedPairBits_numericRouteDescriptors_eq_keyBlocks
    formula wellFormed degree isLocal forward nonempty]
  change (datums.map CarrierNodeRankDatum.key).dedup.flatMap
      (fun key => routeDescriptorRetainedCarrierPairBitsAtPeriod
        period descriptors key) = _
  rw [dedupDatumKeys_numeric_eq_completeKeys formula nonempty]
  have periodEq : period = drawingGridSize formula.incidenceGraph := by
    simpa [period, descriptors] using
      routeDescriptorStreamGridSize_numericRouteDescriptors
        formula nonempty
  rw [periodEq]
  have blockEq :
      (retainedDrawingCompleteCarrierKeys formula.incidenceGraph).flatMap
          (fun key => routeDescriptorRetainedCarrierPairBitsAtPeriod
            (drawingGridSize formula.incidenceGraph) descriptors key) =
        (retainedDrawingCompleteCarrierKeys formula.incidenceGraph).flatMap
          (retainedCarrierLinkBitsAt formula.incidenceGraph
            (carrierLinkNextSlice formula)) := by
    apply List.flatMap_congr
    intro key _keyMember
    exact (retainedCarrierLinkBitsAt_eq_routeDescriptorBits
      formula key).symm
  rw [blockEq]
  unfold retainedCarrierLinkBits retainedCarrierLinkBitsAt
  rw [retainedDrawingCompleteCarrierLinks_eq_keyBlocks,
    List.map_flatMap]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

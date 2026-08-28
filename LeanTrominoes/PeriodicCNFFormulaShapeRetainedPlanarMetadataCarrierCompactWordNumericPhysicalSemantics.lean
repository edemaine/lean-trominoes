/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalRetainedCompactWordPairSemantics

/-! # Numeric compact carrier pairs as physical representative pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Stable numeric key blocks select exactly the physical representative
carrier-node pairs at the formula's drawing period. -/
theorem numericCarrierCompactWordPairs_eq_physicalPairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let keys := (datums.map CarrierNodeRankDatum.key).dedup
    let retainedPairs := fun key =>
      (((CarrierRankGlobal.keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.1.identity.node,
              CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.2.identity.node)
    keys.flatMap retainedPairs =
      (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              fun pair =>
                (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                    (drawingGridSize source.incidenceGraph) pair.1,
                  CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                    (drawingGridSize source.incidenceGraph) pair.2) := by
  let descriptors := numericRouteDescriptors source
  let period := routeDescriptorStreamGridSize descriptors
  let nodes :=
    routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
  let datums :=
    (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
  let keys := (datums.map CarrierNodeRankDatum.key).dedup
  change keys.flatMap _ = _
  rw [CarrierRankGlobal.dedupGlobalRetainedCompactWordPairs_eq_physicalPairs
    period nodes]
  have keysEq :
      keys = retainedDrawingCompleteCarrierKeys source.incidenceGraph := by
    simpa [keys, datums, nodes, routeDescriptorCarrierRankDatumsAtPeriod,
      period, descriptors] using
        dedupDatumKeys_numeric_eq_completeKeys source nonempty
  change keys.flatMap _ = _
  rw [keysEq]
  have periodEq : period = drawingGridSize source.incidenceGraph := by
    simpa [period, descriptors] using
      routeDescriptorStreamGridSize_numericRouteDescriptors source nonempty
  have nodesEq : nodes = retainedDrawingCarrierNodes source.incidenceGraph := by
    change routeDescriptorRetainedCarrierNodesAtPeriod period
      (numericRouteDescriptors source) = _
    rw [periodEq]
    exact routeDescriptorRetainedCarrierNodes_numeric_eq source
  rw [periodEq, nodesEq]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

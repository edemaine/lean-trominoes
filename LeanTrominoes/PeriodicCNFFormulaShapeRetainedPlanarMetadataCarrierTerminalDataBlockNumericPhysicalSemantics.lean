/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalRetainedTerminalDataBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDataBlockKeySemantics

/-! # Numeric carrier terminal blocks as physical representative pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Stable numeric key blocks contain exactly the terminal-data blocks of
the physical representative carrier-node pairs at the drawing period. -/
theorem numericCarrierTerminalDataKeyBlocks_eq_physicalPairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    CarrierRankOrderedPairs.retainedKeyTerminalDataBlocksFromDatums datums =
      (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              fun pair =>
                carrierLensRouteTerminalDataBlock pair.1.isHorizontal
                  (carrierNodeOrderCoordinateAtPeriod
                      (drawingGridSize source.incidenceGraph) pair.2 -
                    carrierNodeOrderCoordinateAtPeriod
                      (drawingGridSize source.incidenceGraph) pair.1) := by
  let descriptors := numericRouteDescriptors source
  let period := routeDescriptorStreamGridSize descriptors
  let nodes :=
    routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
  let datums :=
    (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
  unfold CarrierRankOrderedPairs.retainedKeyTerminalDataBlocksFromDatums
  simp only [CarrierRankOrderedPairs.retainedPairTerminalDataBlock_eq_signedSpan]
  rw [CarrierRankGlobal.dedupGlobalRetainedTerminalDataBlocks_eq_physicalPairs
    period nodes]
  have keysEq :
      (datums.map CarrierNodeRankDatum.key).dedup =
        retainedDrawingCompleteCarrierKeys source.incidenceGraph := by
    simpa [datums, nodes, routeDescriptorCarrierRankDatumsAtPeriod,
      period, descriptors] using
        dedupDatumKeys_numeric_eq_completeKeys source nonempty
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

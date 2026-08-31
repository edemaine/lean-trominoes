/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordGeometryPresentation
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalRetainedGeometrySemantics

/-! # Numeric retained-carrier geometries as physical pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open CarrierFallbackRouteTailRecords

/-- Stable row-major numeric selection gives exactly the finite geometries
of the physical representative carrier-node pairs. -/
theorem numericCarrierGeometries_eq_physicalPairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let entries := CarrierRankGlobal.enumeration datums
    selectedGeometries entries.zipIdx =
      (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              (Geometry.ofNodePairAtPeriod
                (drawingGridSize source.incidenceGraph)) := by
  let descriptors := numericRouteDescriptors source
  let period := routeDescriptorStreamGridSize descriptors
  let nodes :=
    routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
  let datums :=
    (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
  let entries := CarrierRankGlobal.enumeration datums
  dsimp only
  rw [selectedGeometries_eq_filterMap]
  rw [CarrierRankOrderedPairs.retainedRowMajorSelectedWith_eq_keyBlocks
    datums Geometry.ofRankDatums]
  rw [CarrierRankGlobal.dedupGlobalRetainedGeometries_eq_physicalPairs
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

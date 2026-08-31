/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierGeometryNumericPhysicalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierGeometryPhysicalSemantics

/-! # Semantic retained-link meaning of compiler geometries -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open CarrierFallbackRouteTailRecords

/-- On valid numeric routes, row-major selected geometries are exactly the
semantic retained carrier-link geometries in presentation order. -/
theorem numericCarrierGeometries_eq_links
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let entries := CarrierRankGlobal.enumeration datums
    selectedGeometries entries.zipIdx =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (Geometry.ofLink source) := by
  exact (numericCarrierGeometries_eq_physicalPairs
    source nonempty).trans
      (physicalCarrierGeometries_eq_links
        source wellFormed degree isLocal)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

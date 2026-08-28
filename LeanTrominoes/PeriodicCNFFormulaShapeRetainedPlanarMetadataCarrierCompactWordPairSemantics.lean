/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierCompactWordNumericPhysicalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierCompactWordPhysicalNormalizedSemantics

/-! # Compact words selected by the retained carrier-pair mask -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The compact endpoint pairs selected in global stable-rank order are
exactly the compact endpoint pairs of the normalized semantic retained
carrier links, in presentation order. -/
theorem numericCarrierCompactWordPairs_eq_normalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let retainedPairs := fun key =>
      (((CarrierRankGlobal.keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.1.identity.node,
              CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.2.identity.node)
    (datums.map CarrierNodeRankDatum.key).dedup.flatMap retainedPairs =
      ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source))).map fun link =>
            (PeriodicOrthocrossing.RetainedCompactAtomWords.word
                sourceWord link.first,
              PeriodicOrthocrossing.RetainedCompactAtomWords.word
                sourceWord link.second) := by
  exact (numericCarrierCompactWordPairs_eq_physicalPairs
    source nonempty).trans
      (physicalCarrierCompactWordPairs_eq_normalizedLinks
        source sourceWord)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

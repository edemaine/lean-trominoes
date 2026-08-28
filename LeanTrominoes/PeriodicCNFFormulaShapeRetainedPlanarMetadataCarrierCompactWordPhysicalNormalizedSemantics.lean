/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierCompactWordNormalizationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyBlockSemantics

/-! # Physical compact carrier pairs as normalized semantic links -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The physical representative carrier-pair blocks have exactly the compact
endpoint words of the wrapped normalized retained links. -/
theorem physicalCarrierCompactWordPairs_eq_normalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool) :
    (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        (fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              fun pair =>
                (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                    (drawingGridSize source.incidenceGraph) pair.1,
                  CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                    (drawingGridSize source.incidenceGraph) pair.2)) =
      ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source))).map fun link =>
            (RetainedCompactAtomWords.word sourceWord link.first,
              RetainedCompactAtomWords.word sourceWord link.second) := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  rw [retainedDrawingCompleteCarrierLinks_eq_keyBlocks]
  rw [List.map_map, List.map_flatMap]
  apply List.flatMap_congr
  intro key _keyMember
  rw [retainedRepresentativeCarrierLinksAt_eq_nodePairsAtPeriod]
  rw [List.map_map]
  apply List.map_congr_left
  intro pair _pairMember
  simp only [Function.comp_def, PeriodicEquality.normalizeLink,
    carrierNodePairLink]
  rw [compactWordAtPeriod_eq_wrappedNormalization,
    compactWordAtPeriod_eq_wrappedNormalization]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterMatrixSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierCompactWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMaskNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairGlobalSemantics

/-! # Compact carrier-word pairs selected by the numeric retained mask -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Filtering the row-major compact carrier-word square by the compiled
numeric mask yields exactly the normalized semantic retained-link pairs. -/
theorem retainedCompactWordPairsByMask_eq_normalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (forward : source.IsForwardLocal)
    (nonempty : incidencesWithMetadata source ≠ []) :
    let descriptors := numericRouteDescriptors source
    let period := routeDescriptorStreamGridSize descriptors
    let datums :=
      (routeDescriptorCarrierRankDatumsAtPeriod
        period descriptors).dedup
    let entries := CarrierRankGlobal.enumeration datums
    let nodes := entries.map fun entry => entry.1.identity.node
    DelimitedBinaryWordPairBooleanFilter.selectedPairs
        (CarrierRankOrderedPairs.retainedMaskBits descriptors)
        (DelimitedBinaryWordPairProductMachine.pairs
          (GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod
            period nodes)).pairs =
      ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source))).map fun link =>
            (RetainedCompactAtomWords.word sourceWord link.first,
              RetainedCompactAtomWords.word sourceWord link.second) := by
  let descriptors := numericRouteDescriptors source
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  let nodes := entries.map fun entry => entry.1.identity.node
  let word := fun datum : CarrierNodeRankDatum =>
    CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
      period datum.identity.node
  let entryWord := fun entry : CarrierNodeRankDatum × Nat => word entry.1
  have maskEq :
      CarrierRankOrderedPairs.retainedMaskBits descriptors =
        SignedUnaryStrictLower.matrix entries.zipIdx
          CarrierRankOrderedPairs.retainedPredicate := by
    simpa [descriptors, period, datums, entries] using
      CarrierRankOrderedPairs.retainedMaskBits_numericRouteDescriptors
        source wellFormed degree isLocal forward nonempty
  change DelimitedBinaryWordPairBooleanFilter.selectedPairs
    (CarrierRankOrderedPairs.retainedMaskBits descriptors)
    (DelimitedBinaryWordPairProductMachine.pairs
      (GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod
        period nodes)).pairs = _
  rw [maskEq]
  have wordsEq :
      (GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod
        period nodes).words = entries.map entryWord := by
    simp [GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod,
      nodes, entryWord, word, List.map_map]
  unfold DelimitedBinaryWordPairProductMachine.pairs
  rw [wordsEq]
  have zipWordsEq :
      entries.zipIdx.map (fun indexed => entryWord indexed.1) =
        entries.map entryWord := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map entryWord) (List.zipIdx_map_fst 0 entries)
  rw [← zipWordsEq]
  unfold SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  rw [DelimitedBinaryWordPairBooleanFilter.selectedPairs_matrix]
  change (entries.zipIdx.flatMap fun first =>
    entries.zipIdx.filterMap fun second =>
      if CarrierRankOrderedPairs.retainedPredicate first second then
        some (word first.1.1, word second.1.1)
      else none) = _
  rw [CarrierRankOrderedPairs.retainedRowMajorMappedPairs_eq_keyBlocks]
  exact numericCarrierCompactWordPairs_eq_normalizedLinks
    source sourceWord nonempty

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

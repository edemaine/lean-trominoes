/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfilePolarityIndexedRouteOperationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseProfileListSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs

/-! # Polarity operations of complete final Figure 9 token streams -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open UnaryProgramClauseProfile

/-- One directed parent clause's final headers carry exactly the numeric
polarity-operation schedule obtained from its emitted literal-value clauses. -/
theorem sourceClauseHeaders_map_indexedPolarity
    (profile : DirectedClauseProfile) :
    ((sourceClauseHeaders profile).map fun header =>
        header.polarity.indexed) =
      (finalClauseLiteralValueBlock (.clause profile)).flatMap
        indexedDescriptors := by
  rw [show
      (sourceClauseHeaders profile).map
          (fun header => header.polarity.indexed) =
        ((sourceClauseHeaders profile).map Header.polarity).map
          Descriptor.indexed by
    rw [List.map_map]
    rfl]
  rw [sourceClauseHeaders_map_polarity]
  unfold finalClauseLiteralValueBlock
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro generated _generatedMember
  exact descriptors_map_indexed generated

/-- Across a complete directed token list, the direct finite headers retain
the exact per-final-clause source-index and polarity-operation schedule.
Variable markers emit neither clauses nor headers. -/
theorem sourceHeaders_map_indexedPolarity
    (source : List FormulaShapeDirectionOrdering.Token) :
    (FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders source).map
        (fun header => header.polarity.indexed) =
      (source.flatMap finalClauseLiteralValueBlock).flatMap
        indexedDescriptors := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          change
            (FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
              source).map (fun header => header.polarity.indexed) =
              (source.flatMap finalClauseLiteralValueBlock).flatMap
                indexedDescriptors
          exact induction
      | clause profile =>
          rw [show
              FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
                  (.clause profile :: source) =
                sourceClauseHeaders profile ++
                  FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
                    source by rfl,
            List.map_append, List.flatMap_cons, List.flatMap_append,
            sourceClauseHeaders_map_indexedPolarity, induction]

/-- Pairing each finite header with its selected dynamic route tail preserves
the complete source-index and polarity-operation schedule. -/
theorem sourcePairs_map_indexedPolarity
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
        source tailTables).map (fun pair => pair.1.polarity.indexed) =
      (source.flatMap finalClauseLiteralValueBlock).flatMap
        indexedDescriptors := by
  rw [show
      (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
          source tailTables).map
          (fun pair => pair.1.polarity.indexed) =
        ((FormulaShapeFigureNinePolarityRouteTail.sourcePairs
          source tailTables).map Prod.fst).map
            (fun header => header.polarity.indexed) by
    rw [List.map_map]
    rfl]
  rw [FormulaShapeFigureNinePolarityRouteTail.sourcePairs_map_fst]
  exact sourceHeaders_map_indexedPolarity source

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes

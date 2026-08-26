/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackFamilyLookup

/-! # Raw metadata representative of a normalized bend clause -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A canonical base-bend clause selects bend metadata at its first
occurrence in the complete five-family metadata presentation. -/
theorem exists_bendMetadata_global_lookup_of_base_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ baseBendNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata ∧
      ∃ routeBend localClauseIndex,
        metadata.source = .bend routeBend localClauseIndex := by
  have bendMember : clause ∈ bendMetadataNormalizedClauses source := by
    rw [← bendMetadataNormalizedClauses_dedup_eq_base source]
      at clauseMember
    exact List.mem_dedup.mp clauseMember
  rcases exists_bendMetadata_lookup_of_normalized_mem
      source clause bendMember with
    ⟨metadata, bendLookup, bendSource⟩
  let restValues :=
    routedClauseMetadataNormalizedClauses source ++
      routedVariableMetadataNormalizedClauses source
  let restMetadata :=
    drawingPlanarSATRoutedClauseMetadata source ++
      drawingPlanarSATRoutedVariableClauseMetadata source
  have bendLength :
      (drawingPlanarSATBendClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (bendMetadataNormalizedClauses source).length := by
    simp [bendMetadataNormalizedClauses]
  have bendSuffixLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (bendMetadataNormalizedClauses source) restValues
      (drawingPlanarSATBendClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      restMetadata clause metadata bendLength bendMember bendLookup
  have notCarrier :
      clause ∉ carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_bend source))
      carrierMember bendMember
  have carrierLength :
      (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (carrierMetadataNormalizedClauses source).length := by
    simp [carrierMetadataNormalizedClauses]
  have nonCrossoverLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (carrierMetadataNormalizedClauses source)
      (bendMetadataNormalizedClauses source ++ restValues)
      (retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      (drawingPlanarSATBendClauseMetadata
          (Variable := Variable) source.incidenceGraph ++ restMetadata)
      clause metadata carrierLength notCarrier bendSuffixLookup
  have nonCrossoverValuesEq :
      nonCrossoverMetadataNormalizedClauses source =
        carrierMetadataNormalizedClauses source ++
          (bendMetadataNormalizedClauses source ++ restValues) := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [restValues, List.append_assoc]
  rw [← nonCrossoverValuesEq] at nonCrossoverLookup
  have nonCrossoverMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_right _
      (List.mem_append_left _ bendMember)
  have notCrossover :
      clause ∉ crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have crossoverLength :
      (drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (crossoverMetadataNormalizedClauses source).length := by
    simp [crossoverMetadataNormalizedClauses]
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (crossoverMetadataNormalizedClauses source)
      (nonCrossoverMetadataNormalizedClauses source)
      (drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph ++
        (drawingPlanarSATBendClauseMetadata
            (Variable := Variable) source.incidenceGraph ++ restMetadata))
      clause metadata crossoverLength notCrossover nonCrossoverLookup
  rw [← normalizedClauses_eq_crossover_append_nonCrossover source]
    at globalLookup
  have metadataEq :
      retainedDrawingPlanarSATClauseMetadata source =
        drawingPlanarSATCrossoverClauseMetadata
            (Variable := Variable) source.incidenceGraph ++
          (retainedDrawingPlanarSATCarrierClauseMetadata
              (Variable := Variable) source.incidenceGraph ++
            (drawingPlanarSATBendClauseMetadata
                (Variable := Variable) source.incidenceGraph ++
              restMetadata)) := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      restMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact ⟨metadata, globalLookup, bendSource⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

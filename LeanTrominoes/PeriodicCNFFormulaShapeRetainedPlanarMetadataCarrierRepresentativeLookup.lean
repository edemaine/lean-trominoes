/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackFamilyLookup

/-! # Raw metadata representative of a normalized carrier clause -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A normalized retained-carrier clause selects carrier metadata at its
first occurrence in the complete five-family metadata presentation. -/
theorem exists_carrierMetadata_global_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ carrierMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata ∧
      ∃ link localClauseIndex,
        metadata.source = .carrier link localClauseIndex := by
  rcases exists_carrierMetadata_lookup_of_normalized_mem
      source clause clauseMember with
    ⟨metadata, carrierLookup, carrierSource⟩
  let restValues :=
    bendMetadataNormalizedClauses source ++
      routedClauseMetadataNormalizedClauses source ++
        routedVariableMetadataNormalizedClauses source
  let restMetadata :=
    drawingPlanarSATBendClauseMetadata
        (Variable := Variable) source.incidenceGraph ++
      drawingPlanarSATRoutedClauseMetadata source ++
        drawingPlanarSATRoutedVariableClauseMetadata source
  have nonCrossoverValuesEq :
      nonCrossoverMetadataNormalizedClauses source =
        carrierMetadataNormalizedClauses source ++ restValues := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [restValues, List.append_assoc]
  have carrierLength :
      (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (carrierMetadataNormalizedClauses source).length := by
    simp [carrierMetadataNormalizedClauses]
  have nonCrossoverLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (carrierMetadataNormalizedClauses source) restValues
      (retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph) restMetadata
      clause metadata carrierLength clauseMember carrierLookup
  rw [← nonCrossoverValuesEq] at nonCrossoverLookup
  have nonCrossoverMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_left _ clauseMember
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
          (Variable := Variable) source.incidenceGraph ++ restMetadata)
      clause metadata crossoverLength notCrossover nonCrossoverLookup
  rw [← normalizedClauses_eq_crossover_append_nonCrossover source]
    at globalLookup
  have metadataEq :
      retainedDrawingPlanarSATClauseMetadata source =
        drawingPlanarSATCrossoverClauseMetadata
            (Variable := Variable) source.incidenceGraph ++
          (retainedDrawingPlanarSATCarrierClauseMetadata
              (Variable := Variable) source.incidenceGraph ++ restMetadata) := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      restMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact ⟨metadata, globalLookup, carrierSource⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

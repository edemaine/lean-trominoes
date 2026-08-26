/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.ListMapIdxOfPreimage
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix

/-! # Raw metadata representative of a normalized crossover clause -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The first crossover-metadata record normalizing to a crossover clause
records the physical crossing and local clause index that generated it. -/
theorem exists_crossoverMetadata_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ crossoverMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) source.incidenceGraph)[
          (crossoverMetadataNormalizedClauses source).idxOf clause]? =
        some metadata ∧
      normalizedClause source metadata = clause ∧
      ∃ crossing localClauseIndex,
        metadata.source = .crossover crossing localClauseIndex := by
  rcases IndexedListScan.exists_getElem?_idxOf_map
      (drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      (normalizedClause source) clause clauseMember with
    ⟨metadata, metadataLookup, normalizedEq, metadataMember⟩
  refine ⟨metadata, metadataLookup, normalizedEq, ?_⟩
  unfold drawingPlanarSATCrossoverClauseMetadata at metadataMember
  rcases List.mem_flatMap.mp metadataMember with
    ⟨crossing, _crossingMember, metadataMember⟩
  unfold drawingPlanarSATCrossoverClauseMetadataFor at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, _taggedClauseMember, metadataEq⟩
  subst metadata
  exact ⟨crossing, taggedClause.2, rfl⟩

/-- A normalized crossover clause selects crossover metadata at its first
occurrence in the complete five-family metadata presentation. -/
theorem exists_crossoverMetadata_global_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ crossoverMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata ∧
      normalizedClause source metadata = clause ∧
      ∃ crossing localClauseIndex,
        metadata.source = .crossover crossing localClauseIndex := by
  rcases exists_crossoverMetadata_lookup_of_normalized_mem
      source clause clauseMember with
    ⟨metadata, crossoverLookup, normalizedEq, crossoverSource⟩
  let suffixMetadata :=
    retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph ++
      drawingPlanarSATBendClauseMetadata source.incidenceGraph ++
        drawingPlanarSATRoutedClauseMetadata source ++
          drawingPlanarSATRoutedVariableClauseMetadata source
  have crossoverLength :
      (drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (crossoverMetadataNormalizedClauses source).length := by
    simp [crossoverMetadataNormalizedClauses]
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (crossoverMetadataNormalizedClauses source)
      (nonCrossoverMetadataNormalizedClauses source)
      (drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      suffixMetadata clause metadata crossoverLength
      clauseMember crossoverLookup
  rw [← normalizedClauses_eq_crossover_append_nonCrossover source]
    at globalLookup
  have metadataEq :
      retainedDrawingPlanarSATClauseMetadata source =
        drawingPlanarSATCrossoverClauseMetadata
            (Variable := Variable) source.incidenceGraph ++
          suffixMetadata := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      suffixMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact ⟨metadata, globalLookup, normalizedEq, crossoverSource⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

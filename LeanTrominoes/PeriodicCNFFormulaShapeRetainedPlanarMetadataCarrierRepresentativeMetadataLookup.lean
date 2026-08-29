/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRepresentativeLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierMetadataLookup

/-! # Exact global metadata representative of a normalized carrier clause -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A normalized retained-carrier clause selects the exact raw metadata of
its original link and direction in the complete five-family presentation. -/
theorem carrierMetadata_global_lookup_of_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph).product [true, false]) :
    (retainedDrawingPlanarSATClauseMetadata source)[
        (normalizedClauses source).idxOf
          (normalizedCarrierClauseAt source taggedLink)]? =
      some (carrierClauseMetadataAt (Variable := Variable)
        taggedLink.1 taggedLink.2) := by
  let clause := normalizedCarrierClauseAt source taggedLink
  let metadata := carrierClauseMetadataAt
    (Variable := Variable) taggedLink.1 taggedLink.2
  let restValues :=
    bendMetadataNormalizedClauses source ++
      routedClauseMetadataNormalizedClauses source ++
        routedVariableMetadataNormalizedClauses source
  let restMetadata :=
    drawingPlanarSATBendClauseMetadata
        (Variable := Variable) source.incidenceGraph ++
      drawingPlanarSATRoutedClauseMetadata source ++
        drawingPlanarSATRoutedVariableClauseMetadata source
  have carrierMember : clause ∈ carrierMetadataNormalizedClauses source := by
    rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks]
    exact List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have carrierLookup :
      (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph)[
          (carrierMetadataNormalizedClauses source).idxOf clause]? =
        some metadata := by
    exact
      retainedDrawingPlanarSATCarrierClauseMetadata_getElem?_idxOf_normalized
        source taggedLink taggedLinkMember
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
      clause metadata carrierLength carrierMember carrierLookup
  rw [← nonCrossoverValuesEq] at nonCrossoverLookup
  have nonCrossoverMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_left _ carrierMember
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
              (Variable := Variable) source.incidenceGraph ++
            restMetadata) := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      restMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact globalLookup

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

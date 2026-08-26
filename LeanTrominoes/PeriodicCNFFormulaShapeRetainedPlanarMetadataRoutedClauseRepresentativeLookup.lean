/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.ListMapIdxOfPreimage
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRoutedVariableNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseData

/-! # Raw metadata representative of a normalized routed clause -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A normalized routed source clause selects routed-clause metadata at its
first occurrence in the complete five-family metadata presentation.  The
selected raw record retains its exact source clause and physical neighboring
translation. -/
theorem exists_routedClauseMetadata_global_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ routedClauseMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata ∧
      normalizedClause source metadata = clause ∧
      ∃ (taggedClause : PeriodicClause Variable × Nat)
          (translate : Cell),
        taggedClause ∈ source.clauses.zipIdx ∧
        translate ∈ neighborTranslations ∧
        metadata = routedClauseMetadataAt source
          (taggedClause.2, translate) := by
  have mappedMember : clause ∈
      (drawingPlanarSATRoutedClauseMetadata source).map
        (normalizedClause source) := by
    exact clauseMember
  rcases IndexedListScan.exists_getElem?_idxOf_map
      (drawingPlanarSATRoutedClauseMetadata source)
      (normalizedClause source) clause mappedMember with
    ⟨metadata, routedLookup, normalizedEq, metadataMember⟩
  have sourceWitness :
      ∃ (taggedClause : PeriodicClause Variable × Nat)
          (translate : Cell),
        taggedClause ∈ source.clauses.zipIdx ∧
        translate ∈ neighborTranslations ∧
        metadata = routedClauseMetadataAt source
          (taggedClause.2, translate) := by
    rw [drawingPlanarSATRoutedClauseMetadata_eq_map]
      at metadataMember
    rcases List.mem_map.mp metadataMember with
      ⟨site, siteMember, metadataEq⟩
    unfold drawingClauseRouteSites at siteMember
    rcases List.mem_flatMap.mp siteMember with
      ⟨taggedClause, taggedClauseMember, siteMember⟩
    rcases List.mem_map.mp siteMember with
      ⟨translate, translateMember, siteEq⟩
    subst site
    exact ⟨taggedClause, translate, taggedClauseMember,
      translateMember, metadataEq.symm⟩
  let suffixValues := routedVariableMetadataNormalizedClauses source
  let suffixMetadata := drawingPlanarSATRoutedVariableClauseMetadata source
  have routedLength :
      (drawingPlanarSATRoutedClauseMetadata source).length =
        (routedClauseMetadataNormalizedClauses source).length := by
    simp [routedClauseMetadataNormalizedClauses]
  have routedSuffixLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (routedClauseMetadataNormalizedClauses source) suffixValues
      (drawingPlanarSATRoutedClauseMetadata source) suffixMetadata
      clause metadata routedLength clauseMember routedLookup
  have notBend :
      clause ∉ bendMetadataNormalizedClauses source := by
    intro bendMember
    exact (List.disjoint_left.mp
      (bendMetadataNormalizedClauses_disjoint_routedClause source))
      bendMember clauseMember
  have bendLength :
      (drawingPlanarSATBendClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (bendMetadataNormalizedClauses source).length := by
    simp [bendMetadataNormalizedClauses]
  have bendRestLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (bendMetadataNormalizedClauses source)
      (routedClauseMetadataNormalizedClauses source ++ suffixValues)
      (drawingPlanarSATBendClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      (drawingPlanarSATRoutedClauseMetadata source ++ suffixMetadata)
      clause metadata bendLength notBend routedSuffixLookup
  have notCarrier :
      clause ∉ carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_routedClause
        source wellFormed degree isLocal)) carrierMember clauseMember
  have carrierLength :
      (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) source.incidenceGraph).length =
        (carrierMetadataNormalizedClauses source).length := by
    simp [carrierMetadataNormalizedClauses]
  have nonCrossoverLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (carrierMetadataNormalizedClauses source)
      (bendMetadataNormalizedClauses source ++
        (routedClauseMetadataNormalizedClauses source ++ suffixValues))
      (retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph)
      (drawingPlanarSATBendClauseMetadata
          (Variable := Variable) source.incidenceGraph ++
        (drawingPlanarSATRoutedClauseMetadata source ++ suffixMetadata))
      clause metadata carrierLength notCarrier bendRestLookup
  have nonCrossoverValuesEq :
      nonCrossoverMetadataNormalizedClauses source =
        carrierMetadataNormalizedClauses source ++
          (bendMetadataNormalizedClauses source ++
            (routedClauseMetadataNormalizedClauses source ++
              suffixValues)) := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [suffixValues, List.append_assoc]
  rw [← nonCrossoverValuesEq] at nonCrossoverLookup
  have nonCrossoverMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_right _
      (List.mem_append_right _
        (List.mem_append_left _ clauseMember))
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
            (Variable := Variable) source.incidenceGraph ++
          (drawingPlanarSATRoutedClauseMetadata source ++ suffixMetadata)))
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
              (drawingPlanarSATRoutedClauseMetadata source ++
                suffixMetadata))) := by
    simp [retainedDrawingPlanarSATClauseMetadata,
      suffixMetadata, List.append_assoc]
  rw [← metadataEq] at globalLookup
  exact ⟨metadata, globalLookup, normalizedEq, sourceWitness⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

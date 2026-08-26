/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRoutedVariableNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRoutedVariableNormalizedDisjointness

/-! # Global candidate lookup of normalized routed-variable descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A normalized routed-variable implication selects its finite descriptor
at its first occurrence in the complete retained metadata presentation. -/
theorem metadataClauseDescriptorCandidates_idxOf_eq_normalizedRoutedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedLink : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) × Bool)
    (taggedLinkMember : taggedLink ∈
      ((drawingRoutedVariableLinks source).map
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source))).product
        [true, false]) :
    (metadataClauseDescriptorCandidates source)[
        (normalizedClauses source).idxOf
          (PeriodicEquality.normalizedClause taggedLink)]? =
      some (normalizedRoutedVariableClauseDescriptor taggedLink) := by
  let prefixValues :=
    crossoverMetadataNormalizedClauses source ++
      carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source ++
          routedClauseMetadataNormalizedClauses source
  let prefixOutputs :=
    crossoverMetadataClauseDescriptors source ++
      carrierMetadataClauseDescriptors source ++
        bendMetadataClauseDescriptors source ++
          routedClauseMetadataClauseDescriptors source
  have routedVariableMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        routedVariableMetadataNormalizedClauses source := by
    rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
      PeriodicEquality.normalizedFormulaClauses_eq]
    exact List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have nonCrossoverMember :
      PeriodicEquality.normalizedClause taggedLink ∈
        nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [List.mem_append]
    exact Or.inr routedVariableMember
  have notCrossover :
      PeriodicEquality.normalizedClause taggedLink ∉
        crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have notCarrier :
      PeriodicEquality.normalizedClause taggedLink ∉
        carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_routedVariable source))
      carrierMember routedVariableMember
  have notBend :
      PeriodicEquality.normalizedClause taggedLink ∉
        bendMetadataNormalizedClauses source := by
    intro bendMember
    exact (List.disjoint_left.mp
      (bendMetadataNormalizedClauses_disjoint_routedVariable source))
      bendMember routedVariableMember
  have notRoutedClause :
      PeriodicEquality.normalizedClause taggedLink ∉
        routedClauseMetadataNormalizedClauses source := by
    intro routedClauseMember
    exact (List.disjoint_left.mp
      (routedClauseMetadataNormalizedClauses_disjoint_routedVariable source))
      routedClauseMember routedVariableMember
  have prefixNotMember :
      PeriodicEquality.normalizedClause taggedLink ∉ prefixValues := by
    intro prefixMember
    change PeriodicEquality.normalizedClause taggedLink ∈
      ((crossoverMetadataNormalizedClauses source ++
          carrierMetadataNormalizedClauses source) ++
        bendMetadataNormalizedClauses source) ++
          routedClauseMetadataNormalizedClauses source at prefixMember
    rcases List.mem_append.mp prefixMember with prefixBeforeRouted | routedMember
    · rcases List.mem_append.mp prefixBeforeRouted with
        prefixBeforeBend | bendMember
      · rcases List.mem_append.mp prefixBeforeBend with
          crossoverMember | carrierMember
        · exact notCrossover crossoverMember
        · exact notCarrier carrierMember
      · exact notBend bendMember
    · exact notRoutedClause routedMember
  have prefixLength : prefixOutputs.length = prefixValues.length := by
    simp [prefixOutputs, prefixValues,
      crossoverMetadataClauseDescriptors,
      carrierMetadataClauseDescriptors,
      bendMetadataClauseDescriptors,
      routedClauseMetadataClauseDescriptors,
      crossoverMetadataNormalizedClauses,
      carrierMetadataNormalizedClauses,
      bendMetadataNormalizedClauses,
      routedClauseMetadataNormalizedClauses]
  have localLookup :=
    normalizedRoutedVariableClauseDescriptors_getElem?_idxOf
      source taggedLink taggedLinkMember
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      prefixValues
      (routedVariableMetadataNormalizedClauses source)
      prefixOutputs
      (normalizedRoutedVariableClauseDescriptors source)
      (PeriodicEquality.normalizedClause taggedLink)
      (normalizedRoutedVariableClauseDescriptor taggedLink)
      prefixLength prefixNotMember localLookup
  have normalizedClausesEq :
      normalizedClauses source =
        prefixValues ++ routedVariableMetadataNormalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover,
      nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [prefixValues, List.append_assoc]
  have candidatesEq :
      metadataClauseDescriptorCandidates source =
        prefixOutputs ++ normalizedRoutedVariableClauseDescriptors source := by
    rw [metadataClauseDescriptorCandidates_eq_families]
    unfold familyMetadataClauseDescriptors
    rw [routedVariableMetadataClauseDescriptors_eq_normalizedPairs
      source wellFormed isLocal]
  rw [← normalizedClausesEq, ← candidatesEq] at globalLookup
  exact globalLookup

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

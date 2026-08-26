/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedClauseDescriptorLookup

/-! # Public representative descriptors of normalized routed clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- Public first-occurrence selection assigns one base normalized routed
source clause its finite source-clause descriptor. -/
theorem representativeClauseDescriptor_eq_normalizedRoutedClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ source.clauses.zipIdx) :
    representativeClauseDescriptor source
        (normalizedRoutedClauseAt source
          (taggedClause.2, (0, 0))) =
      baseRoutedClauseDescriptorAt taggedClause := by
  let baseClause := normalizedRoutedClauseAt source
    (taggedClause.2, (0, 0))
  let suffixValues := routedVariableMetadataNormalizedClauses source
  let suffixOutputs := routedVariableMetadataClauseDescriptors source
  have taggedSiteMember : (taggedClause, (0, 0)) ∈
      source.clauses.zipIdx.product neighborTranslations := by
    apply List.mem_product.mpr
    exact ⟨taggedClauseMember, by native_decide⟩
  have routedMember : baseClause ∈
      routedClauseMetadataNormalizedClauses source := by
    rw [routedClauseMetadataNormalizedClauses_eq_map_taggedSites]
    exact List.mem_map.mpr
      ⟨(taggedClause, (0, 0)), taggedSiteMember, rfl⟩
  have routedLength :
      (routedClauseMetadataClauseDescriptors source).length =
        (routedClauseMetadataNormalizedClauses source).length := by
    simp [routedClauseMetadataClauseDescriptors,
      routedClauseMetadataNormalizedClauses]
  have routedLookup :=
    routedClauseMetadataClauseDescriptors_getElem?_idxOf_normalized
      source wellFormed clausesNonempty
      (taggedClause, (0, 0)) taggedSiteMember
  have routedSuffixLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (routedClauseMetadataNormalizedClauses source) suffixValues
      (routedClauseMetadataClauseDescriptors source) suffixOutputs
      baseClause (baseRoutedClauseDescriptorAt taggedClause)
      routedLength routedMember routedLookup
  have notBend : baseClause ∉ bendMetadataNormalizedClauses source := by
    intro bendMember
    exact (List.disjoint_left.mp
      (bendMetadataNormalizedClauses_disjoint_routedClause source))
      bendMember routedMember
  have bendLength :
      (bendMetadataClauseDescriptors source).length =
        (bendMetadataNormalizedClauses source).length := by
    simp [bendMetadataClauseDescriptors,
      bendMetadataNormalizedClauses]
  have bendRestLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (bendMetadataNormalizedClauses source)
      (routedClauseMetadataNormalizedClauses source ++ suffixValues)
      (bendMetadataClauseDescriptors source)
      (routedClauseMetadataClauseDescriptors source ++ suffixOutputs)
      baseClause (baseRoutedClauseDescriptorAt taggedClause)
      bendLength notBend routedSuffixLookup
  have notCarrier :
      baseClause ∉ carrierMetadataNormalizedClauses source := by
    intro carrierMember
    exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_routedClause
        source wellFormed degree isLocal)) carrierMember routedMember
  have carrierLength :
      (carrierMetadataClauseDescriptors source).length =
        (carrierMetadataNormalizedClauses source).length := by
    simp [carrierMetadataClauseDescriptors,
      carrierMetadataNormalizedClauses]
  have nonCrossoverLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (carrierMetadataNormalizedClauses source)
      (bendMetadataNormalizedClauses source ++
        (routedClauseMetadataNormalizedClauses source ++ suffixValues))
      (carrierMetadataClauseDescriptors source)
      (bendMetadataClauseDescriptors source ++
        (routedClauseMetadataClauseDescriptors source ++ suffixOutputs))
      baseClause (baseRoutedClauseDescriptorAt taggedClause)
      carrierLength notCarrier bendRestLookup
  have nonCrossoverValuesEq :
      nonCrossoverMetadataNormalizedClauses source =
        carrierMetadataNormalizedClauses source ++
          (bendMetadataNormalizedClauses source ++
            (routedClauseMetadataNormalizedClauses source ++ suffixValues)) := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [suffixValues, List.append_assoc]
  have nonCrossoverOutputsEq :
      nonCrossoverMetadataClauseDescriptors source =
        carrierMetadataClauseDescriptors source ++
          (bendMetadataClauseDescriptors source ++
            (routedClauseMetadataClauseDescriptors source ++ suffixOutputs)) := by
    unfold nonCrossoverMetadataClauseDescriptors
    simp only [suffixOutputs, List.append_assoc]
  rw [← nonCrossoverValuesEq, ← nonCrossoverOutputsEq]
    at nonCrossoverLookup
  have nonCrossoverMember : baseClause ∈
      nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_right _
      (List.mem_append_right _
        (List.mem_append_left _ routedMember))
  have notCrossover :
      baseClause ∉ crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have crossoverLength :
      (crossoverMetadataClauseDescriptors source).length =
        (crossoverMetadataNormalizedClauses source).length := by
    simp [crossoverMetadataClauseDescriptors,
      crossoverMetadataNormalizedClauses]
  have globalLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_not_mem
      (crossoverMetadataNormalizedClauses source)
      (nonCrossoverMetadataNormalizedClauses source)
      (crossoverMetadataClauseDescriptors source)
      (nonCrossoverMetadataClauseDescriptors source)
      baseClause (baseRoutedClauseDescriptorAt taggedClause)
      crossoverLength notCrossover nonCrossoverLookup
  have candidatesEq : metadataClauseDescriptorCandidates source =
      crossoverMetadataClauseDescriptors source ++
        nonCrossoverMetadataClauseDescriptors source := by
    rw [metadataClauseDescriptorCandidates_eq_families]
    unfold familyMetadataClauseDescriptors
      nonCrossoverMetadataClauseDescriptors
    simp only [List.append_assoc]
  rw [← normalizedClauses_eq_crossover_append_nonCrossover,
    ← candidatesEq] at globalLookup
  have normalizedMember : baseClause ∈ normalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover]
    exact List.mem_append_right _ nonCrossoverMember
  have clauseLookup :
      (normalizedClauses source)[
          (normalizedClauses source).idxOf baseClause]? =
        some baseClause :=
    List.getElem?_idxOf normalizedMember
  have candidateLookup :=
    metadataClauseDescriptorCandidates_getElem?_eq source baseClause
      ((normalizedClauses source).idxOf baseClause) clauseLookup
  unfold representativeClauseDescriptor
  exact Option.some.inj (candidateLookup.symm.trans globalLookup)

/-- One finite routed source-clause token per source clause, in source
presentation order. -/
def baseRoutedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  source.clauses.map fun clause =>
    routedClauseDescriptor
      (clause.map fun literal =>
        (⟨false, literal.value⟩ : LiteralProfile))

/-- The indexed base routed-clause descriptor scan forgets exactly its
stable source-position tags. -/
theorem baseRoutedClauseDescriptors_eq_map_zipIdx
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    baseRoutedClauseDescriptors source =
      source.clauses.zipIdx.map baseRoutedClauseDescriptorAt := by
  unfold baseRoutedClauseDescriptors
  let descriptor := fun clause : PeriodicClause Variable =>
    routedClauseDescriptor
      (clause.map fun literal =>
        (⟨false, literal.value⟩ : LiteralProfile))
  calc
    source.clauses.map descriptor =
        (source.clauses.zipIdx.map Prod.fst).map descriptor :=
      congrArg (List.map descriptor)
        (List.zipIdx_map_fst 0 source.clauses).symm
    _ = source.clauses.zipIdx.map (descriptor ∘ Prod.fst) := by
      rw [List.map_map]
    _ = source.clauses.zipIdx.map baseRoutedClauseDescriptorAt := by
      apply List.map_congr_left
      intro taggedClause _taggedClauseMember
      rfl

/-- Mapping public representative selection over the canonical base routed
clauses yields exactly one finite descriptor per source clause. -/
theorem baseRoutedClauseNormalizedClauses_map_representative_eq_descriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (baseRoutedClauseNormalizedClauses source).map
        (representativeClauseDescriptor source) =
      baseRoutedClauseDescriptors source := by
  rw [baseRoutedClauseDescriptors_eq_map_zipIdx]
  unfold baseRoutedClauseNormalizedClauses
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedClause taggedClauseMember
  simp only [Function.comp_apply]
  exact representativeClauseDescriptor_eq_normalizedRoutedClause
    source wellFormed degree isLocal clausesNonempty
      taggedClause taggedClauseMember

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

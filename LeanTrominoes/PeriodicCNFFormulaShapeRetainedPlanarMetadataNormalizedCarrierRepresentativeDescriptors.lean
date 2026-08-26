/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup

/-! # Public representative descriptors of normalized carrier clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Public first-occurrence selection assigns one normalized carrier
implication its aligned carrier metadata descriptor. -/
theorem representativeClauseDescriptor_eq_normalizedCarrier
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph).product [true, false]) :
    representativeClauseDescriptor source
        (normalizedCarrierClauseAt source taggedLink) =
      normalizedCarrierClauseDescriptorAt source taggedLink := by
  let carrierRestValues :=
    bendMetadataNormalizedClauses source ++
      routedClauseMetadataNormalizedClauses source ++
        routedVariableMetadataNormalizedClauses source
  let carrierRestOutputs :=
    bendMetadataClauseDescriptors source ++
      routedClauseMetadataClauseDescriptors source ++
        routedVariableMetadataClauseDescriptors source
  have carrierMember : normalizedCarrierClauseAt source taggedLink ∈
      carrierMetadataNormalizedClauses source := by
    rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks]
    exact List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have nonCrossoverValuesEq :
      nonCrossoverMetadataNormalizedClauses source =
        carrierMetadataNormalizedClauses source ++ carrierRestValues := by
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    simp only [carrierRestValues, List.append_assoc]
  have nonCrossoverOutputsEq :
      nonCrossoverMetadataClauseDescriptors source =
        carrierMetadataClauseDescriptors source ++ carrierRestOutputs := by
    unfold nonCrossoverMetadataClauseDescriptors
    simp only [carrierRestOutputs, List.append_assoc]
  have carrierPrefixLength :
      (carrierMetadataClauseDescriptors source).length =
        (carrierMetadataNormalizedClauses source).length := by
    simp [carrierMetadataClauseDescriptors,
      carrierMetadataNormalizedClauses]
  have carrierLookup :=
    carrierMetadataClauseDescriptors_getElem?_idxOf_normalized
      source taggedLink taggedLinkMember
  have nonCrossoverLookup :=
    IndexedListScan.append_getElem?_idxOf_append_of_mem
      (carrierMetadataNormalizedClauses source) carrierRestValues
      (carrierMetadataClauseDescriptors source) carrierRestOutputs
      (normalizedCarrierClauseAt source taggedLink)
      (normalizedCarrierClauseDescriptorAt source taggedLink)
      carrierPrefixLength carrierMember carrierLookup
  rw [← nonCrossoverValuesEq, ← nonCrossoverOutputsEq]
    at nonCrossoverLookup
  have nonCrossoverMember :
      normalizedCarrierClauseAt source taggedLink ∈
        nonCrossoverMetadataNormalizedClauses source := by
    rw [nonCrossoverValuesEq]
    exact List.mem_append_left _ carrierMember
  have notCrossover : normalizedCarrierClauseAt source taggedLink ∉
      crossoverMetadataNormalizedClauses source := by
    intro crossoverMember
    exact (List.disjoint_left.mp
      (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
        source wellFormed degree isLocal))
      crossoverMember nonCrossoverMember
  have crossoverPrefixLength :
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
      (normalizedCarrierClauseAt source taggedLink)
      (normalizedCarrierClauseDescriptorAt source taggedLink)
      crossoverPrefixLength notCrossover nonCrossoverLookup
  have candidatesEq : metadataClauseDescriptorCandidates source =
      crossoverMetadataClauseDescriptors source ++
        nonCrossoverMetadataClauseDescriptors source := by
    rw [metadataClauseDescriptorCandidates_eq_families]
    unfold familyMetadataClauseDescriptors
      nonCrossoverMetadataClauseDescriptors
    simp only [List.append_assoc]
  rw [← normalizedClauses_eq_crossover_append_nonCrossover,
    ← candidatesEq] at globalLookup
  have normalizedMember : normalizedCarrierClauseAt source taggedLink ∈
      normalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover]
    exact List.mem_append_right _ nonCrossoverMember
  have clauseLookup :
      (normalizedClauses source)[
          (normalizedClauses source).idxOf
            (normalizedCarrierClauseAt source taggedLink)]? =
        some (normalizedCarrierClauseAt source taggedLink) :=
    List.getElem?_idxOf normalizedMember
  have candidateLookup :=
    metadataClauseDescriptorCandidates_getElem?_eq source
      (normalizedCarrierClauseAt source taggedLink)
      ((normalizedClauses source).idxOf
        (normalizedCarrierClauseAt source taggedLink)) clauseLookup
  unfold representativeClauseDescriptor
  exact Option.some.inj (candidateLookup.symm.trans globalLookup)

/-- Mapping public representative selection over the duplicate-free carrier
family reproduces its complete aligned metadata descriptor family. -/
theorem carrierMetadataNormalizedClauses_map_representative_eq_descriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    (carrierMetadataNormalizedClauses source).map
        (representativeClauseDescriptor source) =
      carrierMetadataClauseDescriptors source := by
  rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks,
    carrierMetadataClauseDescriptors_eq_map_taggedLinks,
    List.map_map]
  apply List.map_congr_left
  intro taggedLink taggedLinkMember
  simp only [Function.comp_apply]
  exact representativeClauseDescriptor_eq_normalizedCarrier
    source wellFormed degree isLocal taggedLink taggedLinkMember

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

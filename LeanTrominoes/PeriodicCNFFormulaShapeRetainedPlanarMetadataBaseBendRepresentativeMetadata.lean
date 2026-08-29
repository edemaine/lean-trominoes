/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRepresentativeLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendMetadataExact
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors

/-! # Exact metadata representative of a canonical base bend -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The first metadata representative of a canonical untranslated bend
implication may be translated, but has the same direction and corner ports. -/
theorem exists_baseBendRepresentativeMetadata
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (taggedBend : RouteBend × Bool)
    (taggedBendMember : taggedBend ∈
      (baseRouteBends source).product [true, false]) :
    let clause := normalizedBendClauseAt source taggedBend
    ∃ selectedBend : RouteBend,
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? =
        some (bendClauseMetadataAt source.incidenceGraph
          selectedBend taggedBend.2) ∧
      selectedBend.incomingPort = taggedBend.1.incomingPort ∧
      selectedBend.outgoingPort = taggedBend.1.outgoingPort := by
  let clause := normalizedBendClauseAt source taggedBend
  have clauseMember : clause ∈ baseBendNormalizedClauses source := by
    rw [baseBendNormalizedClauses_eq_map_baseTaggedBends]
    exact List.mem_map.mpr ⟨taggedBend, taggedBendMember, rfl⟩
  rcases exists_bendMetadata_global_lookup_of_base_mem
      source wellFormed degree isLocal clause clauseMember with
    ⟨metadata, metadataLookup, selectedBend, localClauseIndex,
      sourceEq⟩
  have metadataMember : metadata ∈
      retainedDrawingPlanarSATClauseMetadata source :=
    List.mem_iff_getElem?.mpr
      ⟨(normalizedClauses source).idxOf clause, metadataLookup⟩
  have metadataValid :=
    retainedDrawingPlanarSATClauseMetadata_valid source metadataMember
  simp only [DrawingPlanarSATClauseMetadata.RetainedValid, sourceEq]
    at metadataValid
  have metadataCases := bendMetadata_eq_forward_or_backward
    source.incidenceGraph metadata selectedBend localClauseIndex
      sourceEq metadataValid.2
  have bendMember : clause ∈ bendMetadataNormalizedClauses source := by
    rw [← bendMetadataNormalizedClauses_dedup_eq_base source]
      at clauseMember
    exact List.mem_dedup.mp clauseMember
  have normalizedMember : clause ∈ normalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover]
    apply List.mem_append_right
    rw [nonCrossoverMetadataNormalizedClauses_eq_families]
    exact List.mem_append_left _
      (List.mem_append_left _
        (List.mem_append_right _ bendMember))
  have normalizedLookup := List.getElem?_idxOf normalizedMember
  change ((retainedDrawingPlanarSATClauseMetadata source).map
      (normalizedClause source))[
        (normalizedClauses source).idxOf clause]? = some clause
    at normalizedLookup
  rw [List.getElem?_map, metadataLookup] at normalizedLookup
  have normalizedEq : normalizedClause source metadata = clause := by
    exact Option.some.inj normalizedLookup
  rcases taggedBend with ⟨routeBend, direction⟩
  cases direction <;>
    rcases metadataCases with metadataEq | metadataEq
  ·
    rw [metadataEq] at metadataLookup normalizedEq
    have selectedClauseEq :
        normalizedBendClauseAt source (selectedBend, true) =
          normalizedBendClauseAt source (routeBend, false) := by
      rw [normalizedClause_bendClauseMetadataAt_eq] at normalizedEq
      exact normalizedEq
    have taggedEq :=
      PeriodicEquality.normalizedClause_injective selectedClauseEq
    have : true = false := congrArg Prod.snd taggedEq
    exact Bool.noConfusion this
  ·
    rw [metadataEq] at metadataLookup normalizedEq
    have selectedClauseEq :
        normalizedBendClauseAt source (selectedBend, false) =
          normalizedBendClauseAt source (routeBend, false) := by
      rw [normalizedClause_bendClauseMetadataAt_eq] at normalizedEq
      exact normalizedEq
    have taggedEq :=
      PeriodicEquality.normalizedClause_injective selectedClauseEq
    have portsEq := routeBend_ports_eq_of_wrappedNormalizedLink_eq
      source selectedBend routeBend (congrArg Prod.fst taggedEq)
    exact ⟨selectedBend, metadataLookup, portsEq⟩
  ·
    rw [metadataEq] at metadataLookup normalizedEq
    have selectedClauseEq :
        normalizedBendClauseAt source (selectedBend, true) =
          normalizedBendClauseAt source (routeBend, true) := by
      rw [normalizedClause_bendClauseMetadataAt_eq] at normalizedEq
      exact normalizedEq
    have taggedEq :=
      PeriodicEquality.normalizedClause_injective selectedClauseEq
    have portsEq := routeBend_ports_eq_of_wrappedNormalizedLink_eq
      source selectedBend routeBend (congrArg Prod.fst taggedEq)
    exact ⟨selectedBend, metadataLookup, portsEq⟩
  ·
    rw [metadataEq] at metadataLookup normalizedEq
    have selectedClauseEq :
        normalizedBendClauseAt source (selectedBend, false) =
          normalizedBendClauseAt source (routeBend, true) := by
      rw [normalizedClause_bendClauseMetadataAt_eq] at normalizedEq
      exact normalizedEq
    have taggedEq :=
      PeriodicEquality.normalizedClause_injective selectedClauseEq
    have : false = true := congrArg Prod.snd taggedEq
    exact Bool.noConfusion this

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

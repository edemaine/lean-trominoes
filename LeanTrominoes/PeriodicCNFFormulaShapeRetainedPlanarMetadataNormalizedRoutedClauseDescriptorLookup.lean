/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseBaseNodup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClausePresentationSemantics

/-! # First-occurrence lookup of normalized routed-clause descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- A source clause's finite routed-clause descriptor, indexed together with
its stable source position. -/
def baseRoutedClauseDescriptorAt
    {Variable : Type} [DecidableEq Variable]
    (taggedClause : PeriodicClause Variable × Nat) :
    FormulaShapeDirectionOrdering.Token :=
  routedClauseDescriptor
    (taggedClause.1.map fun literal =>
      (⟨false, literal.value⟩ : LiteralProfile))

/-- The routed normalized family is the clause/translation product mapped
through its pointwise normalized clause. -/
theorem routedClauseMetadataNormalizedClauses_eq_map_taggedSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedClauseMetadataNormalizedClauses source =
      (source.clauses.zipIdx.product neighborTranslations).map
        (fun taggedSite => normalizedRoutedClauseAt source
          (taggedSite.1.2, taggedSite.2)) := by
  rw [routedClauseMetadataNormalizedClauses_eq_sites]
  unfold List.product
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rw [List.map_map]
  rfl

/-- Under well-formedness, the routed candidate descriptor family is the
same clause/translation product mapped through its source-clause token. -/
theorem routedClauseMetadataClauseDescriptors_eq_map_taggedSites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed) :
    routedClauseMetadataClauseDescriptors source =
      (source.clauses.zipIdx.product neighborTranslations).map
        (fun taggedSite =>
          baseRoutedClauseDescriptorAt taggedSite.1) := by
  rw [routedClauseMetadataClauseDescriptors_eq_map_sites]
  unfold drawingClauseRouteSites List.product
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro translate _translateMember
  simp only [Function.comp_apply]
  rw [metadataClauseDescriptor_routedClauseMetadataAt_eq]
  unfold canonicalRoutedClauseDescriptor baseRoutedClauseDescriptorAt
  rw [normalizedRoutedClauseAt_literalProfiles_eq_current
      source wellFormed,
    routedClauseCurrentProfiles_eq_taggedClause
      source taggedClause taggedClauseMember translate]

/-- Looking up the descriptor at the first occurrence of a normalized
routed source clause returns its source clause's finite descriptor. -/
theorem routedClauseMetadataClauseDescriptors_getElem?_idxOf_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (clausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (taggedSite : (PeriodicClause Variable × Nat) × Cell)
    (taggedSiteMember : taggedSite ∈
      source.clauses.zipIdx.product neighborTranslations) :
    (routedClauseMetadataClauseDescriptors source)[
        (routedClauseMetadataNormalizedClauses source).idxOf
          (normalizedRoutedClauseAt source
            (taggedSite.1.2, taggedSite.2))]? =
      some (baseRoutedClauseDescriptorAt taggedSite.1) := by
  rw [routedClauseMetadataNormalizedClauses_eq_map_taggedSites,
    routedClauseMetadataClauseDescriptors_eq_map_taggedSites
      source wellFormed]
  let taggedSites := source.clauses.zipIdx.product neighborTranslations
  let normalizedAt := fun taggedSite :
      (PeriodicClause Variable × Nat) × Cell =>
    normalizedRoutedClauseAt source
      (taggedSite.1.2, taggedSite.2)
  let descriptorAt := fun taggedSite :
      (PeriodicClause Variable × Nat) × Cell =>
    baseRoutedClauseDescriptorAt taggedSite.1
  change (taggedSites.map descriptorAt)[
      (taggedSites.map normalizedAt).idxOf
        (normalizedAt taggedSite)]? = _
  have normalizedMember : normalizedAt taggedSite ∈
      taggedSites.map normalizedAt :=
    List.mem_map.mpr ⟨taggedSite, taggedSiteMember, rfl⟩
  have clauseLookup := List.getElem?_idxOf normalizedMember
  rw [List.getElem?_map] at clauseLookup
  cases taggedLookup : taggedSites[
      (taggedSites.map normalizedAt).idxOf
        (normalizedAt taggedSite)]? with
  | none =>
      simp [taggedLookup] at clauseLookup
  | some selected =>
      have selectedMember : selected ∈ taggedSites :=
        List.mem_of_getElem? taggedLookup
      have selectedClauseEq : normalizedAt selected =
          normalizedAt taggedSite := by
        simpa [taggedLookup] using clauseLookup
      have selectedBaseEq :
          normalizedRoutedClauseAt source
              (selected.1.2, (0, 0)) =
            normalizedRoutedClauseAt source
              (taggedSite.1.2, (0, 0)) := by
        calc
          _ = normalizedAt selected :=
            (normalizedRoutedClauseAt_eq_base source wellFormed
              selected.1.2 selected.2).symm
          _ = normalizedAt taggedSite := selectedClauseEq
          _ = _ := normalizedRoutedClauseAt_eq_base
            source wellFormed taggedSite.1.2 taggedSite.2
      have selectedTaggedMember : selected.1 ∈ source.clauses.zipIdx :=
        (List.mem_product.mp selectedMember).1
      have targetTaggedMember : taggedSite.1 ∈ source.clauses.zipIdx :=
        (List.mem_product.mp taggedSiteMember).1
      have baseNodup := baseRoutedClauseNormalizedClauses_nodup
        source wellFormed clausesNonempty
      unfold baseRoutedClauseNormalizedClauses at baseNodup
      have selectedTaggedEq : selected.1 = taggedSite.1 :=
        List.inj_on_of_nodup_map baseNodup
          selectedTaggedMember targetTaggedMember selectedBaseEq
      have descriptorEq : descriptorAt selected =
          descriptorAt taggedSite := by
        unfold descriptorAt
        rw [selectedTaggedEq]
      rw [List.getElem?_map, taggedLookup]
      simpa only [Option.map_some] using congrArg some descriptorEq

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

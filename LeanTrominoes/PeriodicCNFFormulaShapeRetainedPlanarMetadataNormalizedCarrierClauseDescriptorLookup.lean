/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizedFamilyNodup

/-! # First-occurrence lookup of normalized carrier descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The normalized implication clause selected by one raw retained carrier
link and direction. -/
def normalizedCarrierClauseAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  PeriodicEquality.normalizedClause
    (PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source) taggedLink.1,
      taggedLink.2)

/-- The metadata candidate descriptor selected by one raw retained carrier
link and direction. -/
def normalizedCarrierClauseDescriptorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool) :
    FormulaShapeDirectionOrdering.Token :=
  metadataClauseDescriptor source
    (carrierClauseMetadataAt taggedLink.1 taggedLink.2)

/-- The normalized retained-carrier clause family is the raw link/direction
presentation mapped through its pointwise normal form. -/
theorem carrierMetadataNormalizedClauses_eq_map_taggedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    carrierMetadataNormalizedClauses source =
      ((retainedDrawingCompleteCarrierLinks
          source.incidenceGraph).product [true, false]).map
        (normalizedCarrierClauseAt source) := by
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq]
  induction retainedDrawingCompleteCarrierLinks
      source.incidenceGraph with
  | nil => rfl
  | cons link links induction =>
      change
        normalizedCarrierClauseAt source (link, true) ::
            normalizedCarrierClauseAt source (link, false) ::
            (((links.map (PeriodicEquality.normalizeLink
              (carrierWrappedVariableNormalization source))).product
                [true, false]).map PeriodicEquality.normalizedClause) =
          normalizedCarrierClauseAt source (link, true) ::
            normalizedCarrierClauseAt source (link, false) ::
            ((links.product [true, false]).map
              (normalizedCarrierClauseAt source))
      rw [induction]

/-- The retained-carrier candidate descriptor family is the same raw
link/direction presentation mapped through its metadata descriptor. -/
theorem carrierMetadataClauseDescriptors_eq_map_taggedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    carrierMetadataClauseDescriptors source =
      ((retainedDrawingCompleteCarrierLinks
          source.incidenceGraph).product [true, false]).map
        (normalizedCarrierClauseDescriptorAt source) := by
  rw [carrierMetadataClauseDescriptors_eq_flatMap_linkBlocks]
  induction retainedDrawingCompleteCarrierLinks
      source.incidenceGraph with
  | nil => rfl
  | cons link links induction =>
      rw [List.flatMap_cons, carrierLinkClauseDescriptors_eq_pair,
        induction]
      rfl

/-- Looking up the descriptor at the first local occurrence of a normalized
retained-carrier implication returns the descriptor of its raw link and
direction. -/
theorem carrierMetadataClauseDescriptors_getElem?_idxOf_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph).product [true, false]) :
    (carrierMetadataClauseDescriptors source)[
        (carrierMetadataNormalizedClauses source).idxOf
          (normalizedCarrierClauseAt source taggedLink)]? =
      some (normalizedCarrierClauseDescriptorAt source taggedLink) := by
  rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks,
    carrierMetadataClauseDescriptors_eq_map_taggedLinks]
  let taggedLinks :=
    (retainedDrawingCompleteCarrierLinks
      source.incidenceGraph).product [true, false]
  change (taggedLinks.map (normalizedCarrierClauseDescriptorAt source))[
      (taggedLinks.map (normalizedCarrierClauseAt source)).idxOf
        (normalizedCarrierClauseAt source taggedLink)]? = _
  have normalizedClauseMember :
      normalizedCarrierClauseAt source taggedLink ∈
        taggedLinks.map (normalizedCarrierClauseAt source) :=
    List.mem_map.mpr ⟨taggedLink, taggedLinkMember, rfl⟩
  have clauseLookup := List.getElem?_idxOf normalizedClauseMember
  rw [List.getElem?_map] at clauseLookup
  cases taggedLookup : taggedLinks[
      (taggedLinks.map (normalizedCarrierClauseAt source)).idxOf
        (normalizedCarrierClauseAt source taggedLink)]? with
  | none =>
      simp [taggedLookup] at clauseLookup
  | some selected =>
      have selectedMember : selected ∈ taggedLinks :=
        List.mem_of_getElem? taggedLookup
      have selectedClauseEq :
          normalizedCarrierClauseAt source selected =
            normalizedCarrierClauseAt source taggedLink := by
        simpa [taggedLookup] using clauseLookup
      have normalizedTaggedEq :
          (PeriodicEquality.normalizeLink
              (carrierWrappedVariableNormalization source) selected.1,
            selected.2) =
          (PeriodicEquality.normalizeLink
              (carrierWrappedVariableNormalization source) taggedLink.1,
            taggedLink.2) :=
        PeriodicEquality.normalizedClause_injective selectedClauseEq
      have selectedLinkMember :=
        (List.mem_product.mp selectedMember).1
      have taggedLinkRawMember :=
        (List.mem_product.mp taggedLinkMember).1
      have rawLinkEq : selected.1 = taggedLink.1 := by
        apply retainedDrawingCompleteCarrierLinks_normalizeLink_injective_on
          selectedLinkMember taggedLinkRawMember
        exact (carrierWrappedNormalizeLink_eq_iff
          source selected.1 taggedLink.1).mp
            (congrArg Prod.fst normalizedTaggedEq)
      have directionEq : selected.2 = taggedLink.2 :=
        congrArg (fun tagged : PeriodicEquality.NormalizedLink
          (WrappedPeriodicPlanarSATVariable Variable) × Bool => tagged.2)
          normalizedTaggedEq
      have selectedEq : selected = taggedLink :=
        Prod.ext rawLinkEq directionEq
      subst selected
      rw [List.getElem?_map, taggedLookup]
      rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

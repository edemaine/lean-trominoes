/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup

/-! # Exact first-occurrence lookup of normalized carrier metadata -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Raw retained-carrier metadata has the same link-major, forward/backward
presentation as the normalized tagged-link family. -/
theorem retainedDrawingPlanarSATCarrierClauseMetadata_eq_map_taggedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph =
      ((retainedDrawingCompleteCarrierLinks
          source.incidenceGraph).product [true, false]).map
        fun taggedLink =>
          carrierClauseMetadataAt (Variable := Variable)
            taggedLink.1 taggedLink.2 := by
  unfold retainedDrawingPlanarSATCarrierClauseMetadata
  induction retainedDrawingCompleteCarrierLinks
      source.incidenceGraph with
  | nil => rfl
  | cons link links induction =>
      rw [List.flatMap_cons,
        drawingPlanarSATCarrierClauseMetadataFor_eq_pair,
        induction]
      rfl

/-- Looking up raw metadata at the first local occurrence of one normalized
carrier implication returns that exact link and direction's metadata. -/
theorem retainedDrawingPlanarSATCarrierClauseMetadata_getElem?_idxOf_normalized
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        source.incidenceGraph).product [true, false]) :
    (retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) source.incidenceGraph)[
          (carrierMetadataNormalizedClauses source).idxOf
            (normalizedCarrierClauseAt source taggedLink)]? =
      some (carrierClauseMetadataAt (Variable := Variable)
        taggedLink.1 taggedLink.2) := by
  rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks,
    retainedDrawingPlanarSATCarrierClauseMetadata_eq_map_taggedLinks]
  let taggedLinks :=
    (retainedDrawingCompleteCarrierLinks
      source.incidenceGraph).product [true, false]
  let metadataAt := fun tagged : EqualityLink CarrierNode × Bool =>
    carrierClauseMetadataAt (Variable := Variable) tagged.1 tagged.2
  change (taggedLinks.map metadataAt)[
      (taggedLinks.map (normalizedCarrierClauseAt source)).idxOf
        (normalizedCarrierClauseAt source taggedLink)]? =
    some (metadataAt taggedLink)
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

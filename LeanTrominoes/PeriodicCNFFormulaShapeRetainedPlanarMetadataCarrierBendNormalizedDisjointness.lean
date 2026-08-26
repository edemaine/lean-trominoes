/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedFamilyDeduplication
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizedFamilyNodup

/-! # Disjointness of normalized retained carriers and bends -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A selected straight-carrier link cannot normalize to a bend link.  The
carrier endpoints have one common segment-occurrence key, while the bend's
terminal prototypes use consecutive segment indices. -/
theorem retainedCarrierWrappedNormalizedLink_ne_bend
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (carrierLink : EqualityLink CarrierNode)
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
        source.incidenceGraph)
    (routeBend : RouteBend) :
    PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) carrierLink ≠
      wrappedNormalizedRouteBendLink source routeBend := by
  intro wrappedEq
  have rawEq := (carrierWrappedNormalizeLink_eq_iff source
    carrierLink
    (routeBend.equalityLink source.incidenceGraph)).mp wrappedEq
  have firstEq := congrArg
    PeriodicEquality.NormalizedLink.first rawEq
  have secondEq := congrArg
    PeriodicEquality.NormalizedLink.second rawEq
  simp only [RouteBend.normalize_equalityLink_first] at firstEq
  simp only [RouteBend.normalize_equalityLink_second] at secondEq
  rcases (normalizeLink_first_eq_terminal_iff
    source.incidenceGraph carrierLink
    routeBend.incomingTerminal.indexed .finish).mp firstEq with
      ⟨firstTranslate, carrierFirstEq⟩
  rcases (normalizeLink_second_eq_terminal_iff
    source.incidenceGraph carrierLink
    routeBend.outgoingTerminal.indexed .start).mp secondEq with
      ⟨secondTranslate, carrierSecondEq⟩
  have common := retainedDrawingCompleteCarrierLinks_common_key
    source.incidenceGraph carrierLinkMember
  rw [carrierFirstEq, carrierSecondEq] at common
  have segmentIndexEq := congrArg
    (fun key : Nat × Nat × Cell => key.2.1) common
  simp [CarrierNode.carrierKey, SegmentTerminal.carrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    RouteBend.incomingTerminal, RouteBend.outgoingTerminal]
    at segmentIndexEq

/-- No normalized retained straight-carrier clause is a normalized bend
clause. -/
theorem carrierMetadataNormalizedClauses_disjoint_bend
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (carrierMetadataNormalizedClauses source)
      (bendMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause carrierClauseMember bendClauseMember
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at carrierClauseMember
  rw [bendMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at bendClauseMember
  rcases List.mem_map.mp carrierClauseMember with
    ⟨carrierTaggedLink, carrierTaggedMember, carrierClauseEq⟩
  rcases List.mem_map.mp bendClauseMember with
    ⟨bendTaggedLink, bendTaggedMember, bendClauseEq⟩
  have taggedEq : carrierTaggedLink = bendTaggedLink :=
    PeriodicEquality.normalizedClause_injective
      (carrierClauseEq.trans bendClauseEq.symm)
  have carrierNormalizedMember :=
    (List.mem_product.mp carrierTaggedMember).1
  have bendNormalizedMember :=
    (List.mem_product.mp bendTaggedMember).1
  rcases List.mem_map.mp carrierNormalizedMember with
    ⟨carrierLink, carrierLinkMember, carrierLinkEq⟩
  rcases List.mem_map.mp bendNormalizedMember with
    ⟨bendLink, bendLinkMember, bendLinkEq⟩
  rcases List.mem_map.mp bendLinkMember with
    ⟨routeBend, _routeBendMember, routeBendLinkEq⟩
  subst bendLink
  apply retainedCarrierWrappedNormalizedLink_ne_bend
    source carrierLink carrierLinkMember routeBend
  exact carrierLinkEq.trans
    ((congrArg Prod.fst taggedEq).trans bendLinkEq.symm)

/-- Stable deduplication of the carrier-bend prefix keeps the already
duplicate-free carrier family followed by the untranslated bend quotient. -/
theorem carrierBendMetadataNormalizedClauses_dedup_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (carrierMetadataNormalizedClauses source ++
      bendMetadataNormalizedClauses source).dedup =
        carrierMetadataNormalizedClauses source ++
          baseBendNormalizedClauses source := by
  rw [(carrierMetadataNormalizedClauses_disjoint_bend
      source).dedup_append,
    carrierMetadataNormalizedClauses_dedup,
    bendMetadataNormalizedClauses_dedup_eq_base]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

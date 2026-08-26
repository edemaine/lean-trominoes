/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyData

/-! # Carrier/bend clauses are disjoint from routed-variable clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A normalized carrier-node equality link cannot equal a normalized active
routed-variable link: the former has a carrier prototype at its second
endpoint, while the latter has a central atom prototype. -/
theorem carrierWrappedNormalizeLink_ne_routedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (carrierLink : EqualityLink CarrierNode)
    (site : VariableRouteSite Variable)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (routedLinkMember :
      routedLink ∈ routedVariableLinksAt source site) :
    PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) carrierLink ≠
      PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source) routedLink := by
  rcases carrierLink with
    ⟨carrierFirst, carrierSecond, carrierPositions⟩
  intro linksEq
  have secondEq := congrArg
    (fun link => link.second.original) linksEq
  simp only [PeriodicEquality.normalizeLink] at secondEq
  rw [routedVariableLinksAt_second
    source site routedLinkMember] at secondEq
  cases carrierSecond <;>
    simp [carrierWrappedVariableNormalization,
      externalWrappedVariableNormalization,
      normalizePlanarSATVariable,
      planarSATExternalVariableMap] at secondEq

/-- No normalized retained straight-carrier clause is a normalized active
routed-variable clause. -/
theorem carrierMetadataNormalizedClauses_disjoint_routedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (carrierMetadataNormalizedClauses source)
      (routedVariableMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause carrierClauseMember routedClauseMember
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at carrierClauseMember
  rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at routedClauseMember
  rcases List.mem_map.mp carrierClauseMember with
    ⟨carrierTaggedLink, carrierTaggedMember, carrierClauseEq⟩
  rcases List.mem_map.mp routedClauseMember with
    ⟨routedTaggedLink, routedTaggedMember, routedClauseEq⟩
  have taggedEq : carrierTaggedLink = routedTaggedLink :=
    PeriodicEquality.normalizedClause_injective
      (carrierClauseEq.trans routedClauseEq.symm)
  rcases List.mem_product.mp carrierTaggedMember with
    ⟨carrierNormalizedMember, _carrierDirectionMember⟩
  rcases List.mem_map.mp carrierNormalizedMember with
    ⟨carrierLink, _carrierLinkMember, carrierLinkEq⟩
  rcases List.mem_product.mp routedTaggedMember with
    ⟨routedNormalizedMember, _routedDirectionMember⟩
  rcases List.mem_map.mp routedNormalizedMember with
    ⟨routedLink, routedLinkMember, routedLinkEq⟩
  rcases List.mem_flatMap.mp routedLinkMember with
    ⟨site, _siteMember, routedLinkAtMember⟩
  apply carrierWrappedNormalizeLink_ne_routedVariable
    source carrierLink site routedLink routedLinkAtMember
  exact carrierLinkEq.trans
    ((congrArg Prod.fst taggedEq).trans routedLinkEq.symm)

/-- No normalized bend clause is a normalized active routed-variable
clause. -/
theorem bendMetadataNormalizedClauses_disjoint_routedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (bendMetadataNormalizedClauses source)
      (routedVariableMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause bendClauseMember routedClauseMember
  rw [bendMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at bendClauseMember
  rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at routedClauseMember
  rcases List.mem_map.mp bendClauseMember with
    ⟨bendTaggedLink, bendTaggedMember, bendClauseEq⟩
  rcases List.mem_map.mp routedClauseMember with
    ⟨routedTaggedLink, routedTaggedMember, routedClauseEq⟩
  have taggedEq : bendTaggedLink = routedTaggedLink :=
    PeriodicEquality.normalizedClause_injective
      (bendClauseEq.trans routedClauseEq.symm)
  rcases List.mem_product.mp bendTaggedMember with
    ⟨bendNormalizedMember, _bendDirectionMember⟩
  rcases List.mem_map.mp bendNormalizedMember with
    ⟨bendLink, bendLinkMember, bendLinkEq⟩
  rcases List.mem_map.mp bendLinkMember with
    ⟨routeBend, _routeBendMember, routeBendLinkEq⟩
  subst bendLink
  rcases List.mem_product.mp routedTaggedMember with
    ⟨routedNormalizedMember, _routedDirectionMember⟩
  rcases List.mem_map.mp routedNormalizedMember with
    ⟨routedLink, routedLinkMember, routedLinkEq⟩
  rcases List.mem_flatMap.mp routedLinkMember with
    ⟨site, _siteMember, routedLinkAtMember⟩
  apply carrierWrappedNormalizeLink_ne_routedVariable
    source (routeBend.equalityLink source.incidenceGraph)
      site routedLink routedLinkAtMember
  exact bendLinkEq.trans
    ((congrArg Prod.fst taggedEq).trans routedLinkEq.symm)

/-- The combined carrier/bend prefix is disjoint from the normalized active
routed-variable family. -/
theorem carrierBendMetadataNormalizedClauses_disjoint_routedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source)
      (routedVariableMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause prefixMember routedMember
  rcases List.mem_append.mp prefixMember with carrierMember | bendMember
  · exact (List.disjoint_left.mp
      (carrierMetadataNormalizedClauses_disjoint_routedVariable source))
        carrierMember routedMember
  · exact (List.disjoint_left.mp
      (bendMetadataNormalizedClauses_disjoint_routedVariable source))
        bendMember routedMember

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

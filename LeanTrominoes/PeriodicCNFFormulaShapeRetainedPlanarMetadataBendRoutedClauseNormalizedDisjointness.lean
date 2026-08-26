/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedFamilyDeduplication
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalizedTranslation

/-! # Bend clauses are disjoint from routed source clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every literal of a normalized routed source clause names the start
terminal of some routed segment. -/
theorem normalizedRoutedClauseAt_literal_original_eq_terminal_start
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable)}
    (literalMember : literal ∈ normalizedRoutedClauseAt source site) :
    ∃ indexed, literal.atom.original =
      PeriodicPlanarSATVariable.terminal indexed .start := by
  unfold normalizedRoutedClauseAt
    PeriodicClause.anchorNormalize at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨periodicLiteral, periodicLiteralMember, literalEq⟩
  unfold PeriodicEquality.periodicizeClause at periodicLiteralMember
  rcases List.mem_map.mp periodicLiteralMember with
    ⟨sourceLiteral, sourceLiteralMember, periodicLiteralEq⟩
  unfold routedClauseAt at sourceLiteralMember
  rcases List.mem_map.mp sourceLiteralMember with
    ⟨occurrence, _occurrenceMember, sourceLiteralEq⟩
  subst sourceLiteral
  subst periodicLiteral
  subst literal
  exact ⟨(occurrence.sourceTerminal source).indexed, rfl⟩

/-- The wrapped carrier normalization preserves the underlying periodic
carrier prototype at the first endpoint. -/
@[simp] theorem carrierWrappedNormalizeLink_first_original
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) link).first.original =
      periodicCarrierNodeToPlanarSATVariable
        (PeriodicEquality.normalizeLink
          (normalizeCarrierNode source.incidenceGraph) link).first := by
  change (carrierWrappedVariableNormalization source link.first).1.original =
    periodicCarrierNodeToPlanarSATVariable
      (normalizeCarrierNode source.incidenceGraph link.first).1
  rw [carrierWrappedVariableNormalization_eq_gaugeNormalization
    source link.first]
  rfl

/-- The wrapped carrier normalization preserves the underlying periodic
carrier prototype at the second endpoint. -/
@[simp] theorem carrierWrappedNormalizeLink_second_original
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source) link).second.original =
      periodicCarrierNodeToPlanarSATVariable
        (PeriodicEquality.normalizeLink
          (normalizeCarrierNode source.incidenceGraph) link).second := by
  change (carrierWrappedVariableNormalization source link.second).1.original =
    periodicCarrierNodeToPlanarSATVariable
      (normalizeCarrierNode source.incidenceGraph link.second).1
  rw [carrierWrappedVariableNormalization_eq_gaugeNormalization
    source link.second]
  rfl

/-- No normalized bend implication is a normalized routed source clause:
the former contains an incoming finish terminal, while every literal of the
latter is a start terminal. -/
theorem bendMetadataNormalizedClauses_disjoint_routedClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (bendMetadataNormalizedClauses source)
      (routedClauseMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause bendClauseMember routedClauseMember
  rw [bendMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq] at bendClauseMember
  rcases List.mem_map.mp bendClauseMember with
    ⟨bendTaggedLink, bendTaggedMember, bendClauseEq⟩
  rcases bendTaggedLink with ⟨normalizedLink, direction⟩
  rcases List.mem_product.mp bendTaggedMember with
    ⟨normalizedLinkMember, _directionMember⟩
  rcases List.mem_map.mp normalizedLinkMember with
    ⟨bendLink, bendLinkMember, normalizedLinkEq⟩
  rcases List.mem_map.mp bendLinkMember with
    ⟨routeBend, _routeBendMember, bendLinkEq⟩
  subst bendLink
  subst normalizedLink
  rw [routedClauseMetadataNormalizedClauses_eq_sites]
    at routedClauseMember
  rcases List.mem_flatMap.mp routedClauseMember with
    ⟨taggedClause, _taggedClauseMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, routedClauseEq⟩
  let normalizedBendLink :=
    PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source)
      (routeBend.equalityLink source.incidenceGraph)
  let firstLiteral : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨normalizedBendLink.first, (0, 0), direction⟩
  have firstLiteralMember : firstLiteral ∈
      PeriodicEquality.normalizedClause
        (normalizedBendLink, direction) := by
    cases direction <;>
      simp [firstLiteral, PeriodicEquality.normalizedClause]
  have normalizedClauseEq :
      PeriodicEquality.normalizedClause
          (normalizedBendLink, direction) =
        normalizedRoutedClauseAt source
          (taggedClause.2, translate) :=
    bendClauseEq.trans routedClauseEq.symm
  have routedFirstLiteralMember : firstLiteral ∈
      normalizedRoutedClauseAt source
        (taggedClause.2, translate) := by
    rw [← normalizedClauseEq]
    exact firstLiteralMember
  rcases normalizedRoutedClauseAt_literal_original_eq_terminal_start
      source (taggedClause.2, translate) routedFirstLiteralMember with
    ⟨indexed, firstOriginalEq⟩
  have bendFirstOriginal : firstLiteral.atom.original =
      PeriodicPlanarSATVariable.terminal
        routeBend.incomingTerminal.indexed .finish := by
    simp [firstLiteral, normalizedBendLink]
    rfl
  rw [bendFirstOriginal] at firstOriginalEq
  cases firstOriginalEq

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

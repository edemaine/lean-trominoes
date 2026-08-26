/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalizedTranslation
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizedFamilyData

/-! # Routed clauses are disjoint from routed-variable clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every literal of a normalized routed source clause names a terminal
prototype. -/
theorem normalizedRoutedClauseAt_literal_original_eq_terminal
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable)}
    (literalMember : literal ∈ normalizedRoutedClauseAt source site) :
    ∃ indexed endpoint,
      literal.atom.original =
        PeriodicPlanarSATVariable.terminal indexed endpoint := by
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
  refine ⟨(occurrence.sourceTerminal source).indexed,
    (occurrence.sourceTerminal source).endpoint, ?_⟩
  rfl

/-- The second endpoint of a normalized active routed-variable link is its
central atom prototype. -/
theorem normalizedRoutedVariableLink_second_original_eq_atom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMember : link ∈ routedVariableLinksAt source site) :
    (PeriodicEquality.normalizeLink
        (externalWrappedVariableNormalization source) link).second.original =
      PeriodicPlanarSATVariable.atom site.1 := by
  unfold PeriodicEquality.normalizeLink
  rw [routedVariableLinksAt_second source site linkMember]
  rfl

/-- No normalized routed source clause is a normalized active
routed-variable implication clause. -/
theorem routedClauseMetadataNormalizedClauses_disjoint_routedVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List.Disjoint
      (routedClauseMetadataNormalizedClauses source)
      (routedVariableMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause routedClauseMember routedVariableMember
  rw [routedClauseMetadataNormalizedClauses_eq_sites]
    at routedClauseMember
  rcases List.mem_flatMap.mp routedClauseMember with
    ⟨taggedClause, _taggedClauseMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, routedClauseEq⟩
  rw [routedVariableMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq]
    at routedVariableMember
  rcases List.mem_map.mp routedVariableMember with
    ⟨taggedLink, taggedLinkMember, routedVariableClauseEq⟩
  rcases taggedLink with ⟨normalizedLink, direction⟩
  rcases List.mem_product.mp taggedLinkMember with
    ⟨normalizedLinkMember, _directionMember⟩
  rcases List.mem_map.mp normalizedLinkMember with
    ⟨link, linkMember, normalizedLinkEq⟩
  rcases List.mem_flatMap.mp linkMember with
    ⟨site, _siteMember, linkAtMember⟩
  have secondOriginal :=
    normalizedRoutedVariableLink_second_original_eq_atom
      source site link linkAtMember
  have atomLiteral : ∃ literal ∈
      PeriodicEquality.normalizedClause (normalizedLink, direction),
      literal.atom = normalizedLink.second := by
    cases direction with
    | false =>
        refine ⟨⟨normalizedLink.second,
          normalizedLink.relativeOffset, true⟩, ?_, rfl⟩
        simp [PeriodicEquality.normalizedClause]
    | true =>
        refine ⟨⟨normalizedLink.second,
          normalizedLink.relativeOffset, false⟩, ?_, rfl⟩
        simp [PeriodicEquality.normalizedClause]
  rcases atomLiteral with
    ⟨literal, literalMember, literalAtomEq⟩
  have normalizedClauseEq :
      normalizedRoutedClauseAt source
          (taggedClause.2, translate) =
        PeriodicEquality.normalizedClause
          (normalizedLink, direction) :=
    routedClauseEq.trans routedVariableClauseEq.symm
  have literalRoutedMember : literal ∈
      normalizedRoutedClauseAt source
        (taggedClause.2, translate) := by
    rw [normalizedClauseEq]
    exact literalMember
  rcases normalizedRoutedClauseAt_literal_original_eq_terminal
      source (taggedClause.2, translate) literalRoutedMember with
    ⟨indexed, endpoint, terminalEq⟩
  have literalOriginalEqAtom : literal.atom.original =
      PeriodicPlanarSATVariable.atom site.1 := by
    rw [literalAtomEq, ← normalizedLinkEq]
    exact secondOriginal
  rw [terminalEq] at literalOriginalEqAtom
  cases literalOriginalEqAtom

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

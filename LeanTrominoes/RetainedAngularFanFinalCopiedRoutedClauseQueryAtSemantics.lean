/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseDescriptorSemanticsAt
import LeanTrominoes.RetainedAngularFanDirectSourceRoutedClauseChoiceShape
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDirectMetadataQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalRoutedClauseMetadataSemantics

/-! # Exact final query for one routed source clause -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- The exact final query of a normalized routed source clause is the stable
routed-clause direct query on that clause's normalized literal profiles. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_eq_routedClause_of_mem
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (routedClauseMember :
      clause ∈ routedClauseMetadataNormalizedClauses formula) :
    retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex clause =
      retainedFinalDirectRoutedClauseQuery
        (clause.map FormulaShapeDirectionOrdering.literalProfile) := by
  have graphWellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed formula
  have graphDegree : formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal : formula.incidenceGraph.IsLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  rcases exists_finalRoutedClauseMetadata_of_clause_lookup
      formula graphWellFormed graphDegree graphLocal
      clauseIndex clause clauseLookup routedClauseMember with
    ⟨metadata, metadataLookup, normalizedEq, taggedClause,
      translate, taggedClauseMember, _translateMember, metadataEq⟩
  subst metadata
  have queryEq :=
    retainedFinalCopiedClauseQueryOfLiterals_eq_directOfMetadataDescriptor
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex clause clauseLookup
      (routedClauseMetadataAt formula
        (taggedClause.2, translate))
      metadataLookup normalizedEq
      (Or.inr (Or.inl ⟨(taggedClause.2, translate), rfl⟩))
      .routedClause (by
        intro literalIndex rawChoice rawLookup
        exact
          retainedDirectSourceRouteChoice?_routedClause_eq_some_shape
            formula sourceWidth taggedClause taggedClauseMember
            translate literalIndex rawChoice rawLookup)
  have normalizedRoutedEq :
      normalizedRoutedClauseAt formula
          (taggedClause.2, translate) = clause := by
    exact
      (normalizedClause_routedClauseMetadataAt_eq
        formula (taggedClause.2, translate)).symm.trans normalizedEq
  calc
    retainedFinalCopiedClauseQueryOfLiterals formula clauseIndex clause =
        RetainedFinalCopiedClauseQuery.directOfToken .routedClause
          (metadataClauseDescriptor formula
            (routedClauseMetadataAt formula
              (taggedClause.2, translate))) :=
      queryEq
    _ = RetainedFinalCopiedClauseQuery.directOfToken .routedClause
          (routedClauseDescriptor
            (clause.map
              FormulaShapeDirectionOrdering.literalProfile)) := by
      rw [metadataClauseDescriptor_routedClauseMetadataAt_eq]
      unfold canonicalRoutedClauseDescriptor
      rw [normalizedRoutedEq]
    _ = retainedFinalDirectRoutedClauseQuery
          (clause.map
            FormulaShapeDirectionOrdering.literalProfile) := by
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes

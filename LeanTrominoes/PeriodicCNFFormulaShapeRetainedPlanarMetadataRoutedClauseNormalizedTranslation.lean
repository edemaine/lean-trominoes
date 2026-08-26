/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedFamilyData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseCommonOffset
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalization

/-! # Translation quotient of normalized routed source clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The wrapped normalized routed source clause depends only on its source
clause index, not on the explicit neighboring translation. -/
theorem normalizedRoutedClauseAt_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (clauseIndex : Nat) (translate : Cell) :
    normalizedRoutedClauseAt source (clauseIndex, translate) =
      normalizedRoutedClauseAt source (clauseIndex, (0, 0)) := by
  unfold normalizedRoutedClauseAt
  rw [periodicizeRoutedClauseAt_external_eq_commonOffset
      source wellFormed (clauseIndex, translate),
    periodicizeRoutedClauseAt_external_eq_commonOffset
      source wellFormed (clauseIndex, (0, 0))]
  have occurrencesEq :
      clauseRouteOccurrencesAt source (clauseIndex, translate) =
        (clauseRouteOccurrencesAt
          source (clauseIndex, (0, 0))).map
            (fun occurrence => occurrence.periodTranslate translate) := by
    simpa [clauseRouteSitePeriodTranslate, Cell.add] using
      clauseRouteOccurrencesAt_periodTranslate
        source (clauseIndex, (0, 0)) translate
  rw [occurrencesEq]
  cases occurrencesBaseEq :
      clauseRouteOccurrencesAt source (clauseIndex, (0, 0)) with
  | nil => rfl
  | cons first rest =>
      simp [PeriodicClause.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize,
        CNFRouteOccurrence.sourceTerminal_periodTranslate,
        SegmentTerminal.periodTranslate,
        Cell.sub]

/-- The routed-clause normalized metadata family is the clause-major
neighboring-translation expansion of its pointwise normal forms. -/
theorem routedClauseMetadataNormalizedClauses_eq_sites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedClauseMetadataNormalizedClauses source =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        neighborTranslations.map fun translate =>
          normalizedRoutedClauseAt source
            (taggedClause.2, translate) := by
  unfold routedClauseMetadataNormalizedClauses
  rw [drawingPlanarSATRoutedClauseMetadata_eq_map,
    List.map_map]
  unfold drawingClauseRouteSites
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  rw [List.map_map]
  apply List.map_congr_left
  intro translate _translateMember
  exact normalizedClause_routedClauseMetadataAt_eq
    source (taggedClause.2, translate)

/-- After pointwise translation normalization, each source clause presents
nine identical copies of its zero-translation normal form. -/
theorem routedClauseMetadataNormalizedClauses_eq_repeatedBase
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed) :
    routedClauseMetadataNormalizedClauses source =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        neighborTranslations.map fun _ =>
          normalizedRoutedClauseAt source
            (taggedClause.2, (0, 0)) := by
  rw [routedClauseMetadataNormalizedClauses_eq_sites]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  apply List.map_congr_left
  intro translate _translateMember
  exact normalizedRoutedClauseAt_eq_base
    source wellFormed taggedClause.2 translate

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

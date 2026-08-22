/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseCommonOffset

/-! # Current-slice profiles of routed source clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- The source-clause polarity stream with every routed terminal placed in
the current normalized slice. -/
def routedClauseCurrentProfiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) : List LiteralProfile :=
  (clauseRouteOccurrencesAt source site).map fun occurrence =>
    ⟨false, occurrence.incidence.literal.value⟩

/-- Anchoring the common site offset makes every routed source-clause
literal a current-slice profile while preserving its source polarity. -/
theorem normalizedRoutedClauseAt_literalProfiles_eq_current
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (site : ClauseRouteSite) :
    (normalizedRoutedClauseAt source site).map
        FormulaShapeDirectionOrdering.literalProfile =
      routedClauseCurrentProfiles source site := by
  unfold normalizedRoutedClauseAt
  rw [periodicizeRoutedClauseAt_external_eq_commonOffset
    source wellFormed site]
  unfold routedClauseCurrentProfiles
  cases occurrencesEq : clauseRouteOccurrencesAt source site with
  | nil =>
      simp [PeriodicClause.anchorNormalize]
  | cons first rest =>
      simp [PeriodicClause.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize,
        FormulaShapeDirectionOrdering.literalProfile,
        Cell.sub]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

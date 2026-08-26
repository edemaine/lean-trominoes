/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupRepeatedMap
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalizedTranslation

/-! # Exact deduplication of normalized routed source clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- One zero-translation normalized routed clause per source clause, in
source presentation order. -/
def baseRoutedClauseNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  source.clauses.zipIdx.map fun taggedClause =>
    normalizedRoutedClauseAt source
      (taggedClause.2, (0, 0))

/-- Stable deduplication of routed-clause metadata removes the nine physical
translations before performing any genuine deduplication between distinct
source-clause indices. -/
theorem routedClauseMetadataNormalizedClauses_dedup_eq_base_dedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed) :
    (routedClauseMetadataNormalizedClauses source).dedup =
      (baseRoutedClauseNormalizedClauses source).dedup := by
  rw [routedClauseMetadataNormalizedClauses_eq_repeatedBase
    source wellFormed]
  unfold baseRoutedClauseNormalizedClauses
  exact List.dedup_flatMap_repeated_map
    source.clauses.zipIdx neighborTranslations
    (fun taggedClause => normalizedRoutedClauseAt source
      (taggedClause.2, (0, 0))) (by
        simp [neighborTranslations, neighborCoordinates])

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

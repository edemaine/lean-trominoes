/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRoutedVariableNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRoutedClauseNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseBaseNodup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseRoutedVariableNormalizedDisjointness

/-! # Exact deduplication of the four non-crossover families -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Stable deduplication of the non-crossover suffix splits across all four
pairwise-disjoint families and applies each established local quotient. -/
theorem nonCrossoverMetadataNormalizedClauses_dedup_eq_families
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (nonCrossoverMetadataNormalizedClauses source).dedup =
      carrierMetadataNormalizedClauses source ++
        baseBendNormalizedClauses source ++
          baseRoutedClauseNormalizedClauses source ++
            (routedVariableMetadataNormalizedClauses source).dedup := by
  have carrierBendDisjointRoutedClause : List.Disjoint
      (carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source)
      (routedClauseMetadataNormalizedClauses source) := by
    rw [List.disjoint_append_left]
    exact ⟨
      carrierMetadataNormalizedClauses_disjoint_routedClause
        source wellFormed degree isLocal,
      bendMetadataNormalizedClauses_disjoint_routedClause source⟩
  have carrierBendRoutedClauseDisjointVariable : List.Disjoint
      (carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source ++
          routedClauseMetadataNormalizedClauses source)
      (routedVariableMetadataNormalizedClauses source) := by
    rw [List.disjoint_append_left, List.disjoint_append_left]
    exact ⟨
      ⟨carrierMetadataNormalizedClauses_disjoint_routedVariable source,
        bendMetadataNormalizedClauses_disjoint_routedVariable source⟩,
      routedClauseMetadataNormalizedClauses_disjoint_routedVariable source⟩
  rw [nonCrossoverMetadataNormalizedClauses_eq_families]
  rw [carrierBendRoutedClauseDisjointVariable.dedup_append,
    carrierBendDisjointRoutedClause.dedup_append,
    carrierBendMetadataNormalizedClauses_dedup_eq,
    routedClauseMetadataNormalizedClauses_dedup_eq_base
      source wellFormed clausesNonempty]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

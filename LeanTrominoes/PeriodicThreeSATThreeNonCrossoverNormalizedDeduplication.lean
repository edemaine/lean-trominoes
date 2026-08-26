/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedDeduplication
import LeanTrominoes.PeriodicThreeSATThreeGraph
import LeanTrominoes.PeriodicThreeSATThreeNonempty
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCanonicalNormalizedClauses

/-! # Non-crossover normalized quotient after occurrence splitting -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance nonCrossoverWrappedDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable)) :=
  inferInstance

/-- For a valid width-three local source, the complete non-crossover suffix
deduplicates to the three established base families followed by the canonical
final-site routed-variable clauses. -/
theorem nonCrossoverMetadataNormalizedClauses_formula_dedup_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (nonCrossoverMetadataNormalizedClauses (formula source)).dedup =
      carrierMetadataNormalizedClauses (formula source) ++
        baseBendNormalizedClauses (formula source) ++
          baseRoutedClauseNormalizedClauses (formula source) ++
            canonicalWrappedNormalizedRoutedVariableClauses source := by
  rw [nonCrossoverMetadataNormalizedClauses_dedup_eq_families
    (formula source)
    (formula_incidenceGraph_isWellFormed source)
    (formula_incidenceGraph_degreeAtMostThree sourceWidth)
    (formula_incidenceGraph_isLocal sourceLocal)
    (formula_clausesNonempty source sourceClausesNonempty)]
  rw [routedVariableMetadataNormalizedClauses_formula_dedup_eq_canonical
    source positiveOffsets]

end LeanTrominoes.PeriodicThreeSATThree

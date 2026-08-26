/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation
import LeanTrominoes.PeriodicThreeSATThreeNonCrossoverNormalizedDeduplication

/-! # Non-crossover family presentation of exact final copied queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

local instance retainedFinalNonCrossoverFamilyThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fun first second => instDecidableEqProd first second

/-- For an occurrence-split formula, the exact indexed non-crossover query
suffix separates into carrier, bend, routed-clause, and routed-variable
families with their accumulated global index offsets. -/
theorem retainedFinalIndexedNonCrossoverClauseQueries_eq_families
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈
      PeriodicThreeSATThree.occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (start : Nat) :
    retainedFinalIndexedClauseQueriesFrom
        (PeriodicThreeSATThree.formula source) start
        (PeriodicThreeSATThree.formulaNonCrossoverMetadataNormalizedClausesDedup
          source) =
      retainedFinalIndexedClauseQueriesFrom
          (PeriodicThreeSATThree.formula source) start
          (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
            source) ++
        retainedFinalIndexedClauseQueriesFrom
            (PeriodicThreeSATThree.formula source)
            (start +
              (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
                source).length)
            (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
              source) ++
          retainedFinalIndexedClauseQueriesFrom
              (PeriodicThreeSATThree.formula source)
              ((start +
                (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
                  source).length) +
                (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
                  source).length)
              (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
                source) ++
            retainedFinalIndexedClauseQueriesFrom
              (PeriodicThreeSATThree.formula source)
              (((start +
                  (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
                    source).length) +
                (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
                  source).length) +
                (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
                  source).length)
              (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
                source) := by
  let transform :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable
          (ThreeOccurrenceVariable Variable))) →
        List RetainedFinalCopiedClauseQuery :=
    retainedFinalIndexedClauseQueriesFrom
      (PeriodicThreeSATThree.formula source) start
  have familyQueriesEq :=
    PeriodicThreeSATThree.formulaNonCrossoverMetadataNormalizedClausesDedup_congr
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      transform
  change transform
      (PeriodicThreeSATThree.formulaNonCrossoverMetadataNormalizedClausesDedup
        source) = _
  calc
    transform
          (PeriodicThreeSATThree.formulaNonCrossoverMetadataNormalizedClausesDedup
            source) = _ := familyQueriesEq
    _ = _ := by
      unfold transform
      rw [retainedFinalIndexedClauseQueriesFrom_append,
        retainedFinalIndexedClauseQueriesFrom_append,
        retainedFinalIndexedClauseQueriesFrom_append]
      simp only [List.length_append, Nat.add_assoc]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

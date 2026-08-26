/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryNonCrossoverFamilyPresentation

/-! # Complete five-family presentation of exact final copied queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance retainedFinalFiveFamilyThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fun first second => instDecidableEqProd first second

/-- For a valid occurrence-split source, the exact final query stream splits
into crossover, carrier, bend, routed-clause, and routed-variable families,
with every family's original global clause indices retained. -/
theorem retainedFinalIndexedClauseQueries_formula_eq_fiveFamilies
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈
      PeriodicThreeSATThree.occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let formula := PeriodicThreeSATThree.formula source
    let crossoverClauses :=
      crossoverMetadataNormalizedClausesDedup formula
    let carrierClauses :=
      PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source
    let bendClauses :=
      PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source
    let routedClauses :=
      PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses source
    retainedFinalIndexedClauseQueries formula =
      retainedFinalIndexedClauseQueriesFrom formula 0 crossoverClauses ++
        retainedFinalIndexedClauseQueriesFrom formula
            crossoverClauses.length carrierClauses ++
          retainedFinalIndexedClauseQueriesFrom formula
              (crossoverClauses.length + carrierClauses.length)
              bendClauses ++
            retainedFinalIndexedClauseQueriesFrom formula
                ((crossoverClauses.length + carrierClauses.length) +
                  bendClauses.length)
                routedClauses ++
              retainedFinalIndexedClauseQueriesFrom formula
                (((crossoverClauses.length + carrierClauses.length) +
                  bendClauses.length) + routedClauses.length)
                (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
                  source) := by
  dsimp only
  rw [retainedFinalIndexedClauseQueries_eq_crossover_append_nonCrossover
    (PeriodicThreeSATThree.formula source)
    (PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source)
    (PeriodicThreeSATThree.formula_incidenceGraph_degreeAtMostThree
      sourceWidth)
    (PeriodicThreeSATThree.formula_incidenceGraph_isLocal sourceLocal)]
  have nonCrossoverClausesEq :
      nonCrossoverMetadataNormalizedClausesDedup
          (PeriodicThreeSATThree.formula source) =
        PeriodicThreeSATThree.formulaNonCrossoverMetadataNormalizedClausesDedup
          source := by
    rfl
  rw [nonCrossoverClausesEq]
  rw [retainedFinalIndexedNonCrossoverClauseQueries_eq_families
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]
  simp only [List.append_assoc]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

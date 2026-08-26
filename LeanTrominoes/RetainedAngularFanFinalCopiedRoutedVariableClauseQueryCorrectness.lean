/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCanonicalRoutedVariableQueryQuotient
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedVariableClauseQuerySemantics

/-! # Final routed-variable query correctness -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance finalRoutedVariableCorrectnessThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The final indexed routed-variable clause family is exactly one stable
six-query site block per source literal occurrence. -/
theorem retainedFinalRoutedVariableClauseQueries_formula_eq_fullSites
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
    let start :=
      (((crossoverMetadataNormalizedClausesDedup formula).length +
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          source).length) +
        (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
          source).length) +
      (PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
        source).length
    retainedFinalIndexedClauseQueriesFrom formula start
        (PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
          source) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun _targetIndex =>
          retainedFinalDirectRoutedVariableFullSiteQueries) := by
  dsimp only
  rw [retainedFinalRoutedVariableClauseQueries_formula_eq
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]
  exact PeriodicThreeSATThree.canonicalRoutedVariableQueries_eq_fullSites
    source positiveOffsets

end PeriodicEightOccurrenceSplit
end LeanTrominoes

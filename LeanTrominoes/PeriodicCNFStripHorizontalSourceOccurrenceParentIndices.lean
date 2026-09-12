/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedParentIndexCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences
import LeanTrominoes.FirstParentInheritedRouteCompiler

/-! # Parent index scans agree with coherent source occurrences -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderCopiedParentIndex
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

private theorem expectedAux_eq_parent_rows (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection))) :
    expectedAux parent source =
      (sourceOccurrencesFrom parent start source tails).map SourceOccurrence.parentClauseIndex := by
  induction source generalizing parent start tails with
  | nil => rfl
  | cons token source induction =>
    cases token with
    | «variable» => simpa only [expectedAux, sourceOccurrencesFrom] using induction parent start tails
    | clause profile =>
      have nonzero : (sourceClauseHeaders profile).length ≠ 0 :=
        Nat.ne_of_gt (Nat.zero_lt_of_lt (FirstParentInheritedRoute.index_lt profile))
      simp only [expectedAux, HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock, List.length_map,
        nextParent, nonzero, ↓reduceIte, sourceOccurrencesFrom, List.map_append,
        List.map_map, Function.comp_def, List.map_const']
      rw [induction (parent + 1) (start + generatedClauseCount profile) tails.tail]

/-- The copied-parent scan works for every parent descriptor, including the
cycle suffix, and counts the original parent rather than generated clauses. -/
theorem parentIndices_eq_sourceOccurrences (source : List Token) (tails : List (List (List AxisDirection))) :
    parentIndices source = (sourceOccurrences source tails).map SourceOccurrence.parentClauseIndex := by
  rw [parentIndices_eq_expected]
  exact expectedAux_eq_parent_rows 0 0 source tails

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderCopiedParentIndex

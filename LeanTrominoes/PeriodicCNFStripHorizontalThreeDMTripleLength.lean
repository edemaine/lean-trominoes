/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceRouteLookup
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseTripleIndex

/-! # Alignment of horizontal numbered and typed triple lengths -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The executable numbered problem and its source typed enumeration have
the same number of triples. -/
@[simp] theorem horizontalNormalizationInputComputed_triples_length
    (source : PeriodicCNF Nat) :
    (horizontalNormalizationInputComputed source).problem.triples.length =
      (horizontalThreeDMTypedTriplesComputed source).length := by
  rw [horizontalNormalizationInputComputed_problem]
  unfold horizontalThreeDMProblemComputed
    horizontalThreeDMTypedTriplesComputed
  exact encodedProblem_triples_length
    (horizontalNormalizedRoutedFormulaComputed source).erase

end PeriodicCNFStripReduction
end LeanTrominoes

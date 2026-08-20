/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData

/-! # Semantic form of computed occurrence translations -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceTranslationComputed_eq_data
    (input : HorizontalOccurrenceRouteSomeInput) :
    horizontalOccurrenceTranslationComputed input =
      ((horizontalRoutedPlacementComputed input.1.1.1).scale 2).translation
        (Cell.sub
          (PeriodicCNF.clauseAnchor
            (horizontalOccurrenceClauseComputed input))
          input.2.1.offset) := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

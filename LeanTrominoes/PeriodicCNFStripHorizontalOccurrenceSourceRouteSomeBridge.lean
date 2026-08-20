/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceTranslationBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceReversedRouteBridge

/-! # Semantic form of found horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceSourceRouteSomeComputed_eq_data
    (input : HorizontalOccurrenceRouteSomeInput) :
    horizontalOccurrenceSourceRouteSomeComputed input =
      PeriodicOrthocrossing.translatePolyline
        (((horizontalRoutedPlacementComputed input.1.1.1).scale 2).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor
              (horizontalOccurrenceClauseComputed input))
            input.2.1.offset))
        ((PositionedPeriodicCNF.scaleIncidenceRoutes 2
          (horizontalRoutedRoutesComputed input.1.1.1)
          input.2.2.1 input.2.2.2).reverse) := by
  rw [horizontalOccurrenceSourceRouteSomeComputed,
    horizontalOccurrenceTranslationComputed_eq_data,
    horizontalOccurrenceReversedRouteComputed_eq_data]

end PeriodicCNFStripReduction
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteData

/-! # Semantic form of computed reversed occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceReversedRouteComputed_eq_data
    (input : HorizontalOccurrenceRouteSomeInput) :
    horizontalOccurrenceReversedRouteComputed input =
      (PositionedPeriodicCNF.scaleIncidenceRoutes 2
        (horizontalRoutedRoutesComputed input.1.1.1)
        input.2.2.1 input.2.2.2).reverse := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

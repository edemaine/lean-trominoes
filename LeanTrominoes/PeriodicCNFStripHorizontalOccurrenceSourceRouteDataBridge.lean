/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteSomeBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceSourceRouteData

/-! # Generic interpretation of computed horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The factored horizontal computation is definitionally the generic
proof-free rebasing algorithm on the exact normalized source data. -/
theorem horizontalOccurrenceSourceRouteComputed_eq_data
    (input : HorizontalOccurrenceRouteInput) :
    horizontalOccurrenceSourceRouteComputed input =
      occurrenceSourceRouteFromData
        (horizontalNormalizedRoutedFormulaComputed input.1.1)
        ((horizontalRoutedPlacementComputed input.1.1).scale 2)
        (PositionedPeriodicCNF.scaleIncidenceRoutes 2
          (horizontalRoutedRoutesComputed input.1.1))
        (input.1.2, input.2) := by
  unfold occurrenceSourceRouteFromData
  generalize lookup : occurrenceAt
      (horizontalNormalizedRoutedFormulaComputed input.1.1).erase
      input.1.2 input.2 = result
  cases result with
  | none =>
      simp [horizontalOccurrenceSourceRouteComputed,
        horizontalOccurrenceLookupComputed,
        horizontalOccurrenceLookupInput, lookup]
  | some tagged =>
      rw [show
        horizontalOccurrenceSourceRouteComputed input =
          horizontalOccurrenceSourceRouteSomeComputed (input, tagged) by
            simp [horizontalOccurrenceSourceRouteComputed,
              horizontalOccurrenceLookupComputed,
              horizontalOccurrenceLookupInput, lookup]]
      exact horizontalOccurrenceSourceRouteSomeComputed_eq_data
        (input, tagged)

end PeriodicCNFStripReduction
end LeanTrominoes

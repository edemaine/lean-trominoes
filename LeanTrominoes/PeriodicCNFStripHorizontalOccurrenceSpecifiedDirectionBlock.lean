/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteDirectionBlock

/-! # Exact horizontal geometry for the compiler's specified compact block -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget

/-- Any specified compact block representing the selected stored route word
renders the actual complete coordinated occurrence route. -/
theorem horizontalOccurrenceCoordinatedRoute_directionBlock_eq_of_lookup
    (input : HorizontalOccurrenceColoredRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input.1 = some tagged)
    (block : HorizontalRoutedRouteDirectionBlock)
    (storedWord : block.directions PeriodicOrthocrossing.RetainedFigureNineRouteDirectionBlock.directions =
      unitSubdivisionDirections (horizontalOccurrenceStoredRouteComputed (input.1, tagged))) :
    unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed input) =
      horizontalOccurrenceCoordinatedDirections input block := by
  rw [horizontalOccurrenceCoordinatedRoute_directions_of_lookup input tagged lookup,
    horizontalOccurrenceRibbonCorridor_directions_of_lookup input tagged lookup,
    horizontalOccurrenceUnitSourceRoute_directions_of_lookup input.1 tagged lookup,
    ← storedWord]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end

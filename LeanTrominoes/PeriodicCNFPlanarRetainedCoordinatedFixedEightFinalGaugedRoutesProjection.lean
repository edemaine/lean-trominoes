/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans

/-! # Route projection of the final gauged retained presentation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance routesProjectionVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The final gauged presentation stores the canonical route family supplied
to its constructor. -/
theorem retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation_routes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routes =
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty := by
  simp only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation]

end PeriodicOrthocrossing
end LeanTrominoes

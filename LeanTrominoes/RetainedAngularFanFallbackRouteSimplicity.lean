/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation

/-! # Simplicity components for retained fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Scaling a simple source route and deleting its old variable endpoint
leaves a simple fallback source prefix. -/
theorem retainedFallbackSourcePrefix_isSimple
    (route : List Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedFallbackSourcePrefix route) := by
  have refinedSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (scalePolyline retainedTerminalFanTotalRefinement route) :=
    routeIsSimple_scalePolyline (by native_decide) simple
  have reversed := refinedSimple.reverse.tail.reverse
  rw [← List.dropLast_reverse
    (l := (scalePolyline
      retainedTerminalFanTotalRefinement route).reverse)] at reversed
  simpa [retainedFallbackSourcePrefix] using reversed

end PeriodicEightOccurrenceSplit
end LeanTrominoes

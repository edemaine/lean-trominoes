/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.RetainedAngularFanFallbackSingletonNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData
import LeanTrominoes.RetainedRayRasterizationTranslation

/-! # Translation of singleton-prefix normalized fallbacks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Translating a singleton-prefix source route leaves its canonical
normalized fallback direction word unchanged. -/
theorem RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_translate_normalized_directions
    {factor : Nat}
    (kind : RetainedFallbackFanKind)
    (offset : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (factorPositive : 0 < factor)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeSimple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid
      (scaleRetainedTerminalData factor terminal))
    (singletonPrefix : route.dropLast.length = 1) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route
            (scalePolyline factor
              (translatePolyline offset route))
            (scaleRetainedTerminalData factor terminal) slot)) =
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route)) ++
        retainedNormalizedFallbackFanSuffixDirections kind
          (scaleRetainedTerminalData factor terminal) slot := by
  let translatedRoute := translatePolyline offset route
  have translatedLength : 2 ≤ translatedRoute.length := by
    simpa [translatedRoute, translatePolyline] using routeLength
  have translatedClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector translatedRoute) =
        some terminal := by
    simpa [translatedRoute, routeTerminalVector_translatePolyline] using
      classified
  have translatedSimple :
      LocalIncidenceDrawing.RouteIsSimple translatedRoute := by
    simpa [translatedRoute, translatePolyline] using
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        routeSimple offset
  have translatedOrthogonal : OrthogonalPolyline translatedRoute := by
    simpa [translatedRoute] using routeOrthogonal.translate offset
  have translatedSingleton : translatedRoute.dropLast.length = 1 := by
    simpa [translatedRoute, translatePolyline, List.map_dropLast] using
      singletonPrefix
  have normalized :=
    kind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
      translatedRoute terminal slot factorPositive translatedLength
      translatedClassified translatedSimple translatedOrthogonal
      terminalLengthPositive valid translatedSingleton
  rw [retainedFallbackSourcePrefix_scaled_directions
      factor factorPositive translatedRoute] at normalized
  rw [retainedFallbackSourcePrefix_scaled_directions
      factor factorPositive route]
  have translatedDropLast :
      translatedRoute.dropLast =
        translatePolyline offset route.dropLast := by
    simp [translatedRoute, translatePolyline, List.map_dropLast]
  rw [translatedDropLast,
    Gadget.unitSubdivisionDirections_translatePolyline] at normalized
  simpa [translatedRoute] using normalized

end PeriodicEightOccurrenceSplit
end LeanTrominoes

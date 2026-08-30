/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplatePrefixDirections
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateGeometry
import LeanTrominoes.RetainedAngularFanFallbackNormalizedDirectionExtensionality

/-! # Directional extensionality against canonical carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- Any scaled source route with the canonical carrier prefix and terminal
datum normalizes to the exact finite carrier-record word. -/
theorem carrierRoute_normalized_fallback_directions_eq
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (routeLength : 2 ≤ route.length)
    (routeClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData geometry.horizontal geometry.span
            localClauseIndex literalIndex)))
    (routeOrthogonal : OrthogonalPolyline route)
    (routePrefixDirections :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections
            geometry.horizontal geometry.span
            localClauseIndex literalIndex)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              localClauseIndex literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData geometry.horizontal geometry.span
                localClauseIndex literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        geometry localClauseIndex literalIndex slot := by
  let template :=
    carrierLensTemplateRoute geometry.horizontal geometry.span
      localClauseIndex literalIndex
  let scaledTemplate :=
    scalePolyline retainedAngularFanSourceClearanceFactor template
  let terminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (carrierLensRouteTerminalData geometry.horizontal geometry.span
        localClauseIndex literalIndex)
  have templateLength : 2 ≤ scaledTemplate.length := by
    simpa [scaledTemplate, template, scalePolyline] using
      carrierLensTemplateRoute_length
        geometry localClauseIndex literalIndex
  have templateClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledTemplate) =
        some terminal := by
    exact routeTerminalVector_scale_classified
      retainedAngularFanSourceClearanceFactor_pos
      (carrierLensTemplateRoute_carrier_classified
        geometry spanLarge localClauseIndex literalIndex)
  have templateOrthogonal : OrthogonalPolyline scaledTemplate := by
    exact (carrierLensTemplateRoute_orthogonal
      geometry spanLarge localClauseIndex literalIndex).scalePolyline
        (by native_decide)
  have terminalPositive : 0 < terminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      (carrierLensRouteTerminalData_positive
        geometry spanLarge localClauseIndex literalIndex)
  have valid :
      (CarrierFallbackRouteTailRecords.routeKind
        localClauseIndex literalIndex).Valid terminal := by
    exact carrierLensRouteFallback_valid
      geometry spanLarge localClauseIndex literalIndex
  have templatePrefixDirections :=
    carrierLensTemplateFallbackSourcePrefix_directions_eq
      geometry spanLarge localClauseIndex literalIndex
  have prefixDirectionsEq :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix scaledTemplate) :=
    routePrefixDirections.trans templatePrefixDirections.symm
  calc
    _ = Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            ((CarrierFallbackRouteTailRecords.routeKind
                localClauseIndex literalIndex).splicedOwnFigure7Route
              scaledTemplate terminal slot)) :=
      RetainedFallbackFanKind.splicedOwnFigure7Route_normalized_directions_eq_of_sourcePrefix_directions_eq
        (CarrierFallbackRouteTailRecords.routeKind
          localClauseIndex literalIndex)
        route scaledTemplate terminal slot
        routeLength templateLength routeClassified templateClassified
        routeOrthogonal templateOrthogonal terminalPositive valid
        prefixDirectionsEq
    _ = _ := carrierLensTemplateRoute_normalized_fallback_directions
      geometry spanLarge localClauseIndex literalIndex slot

end PeriodicEightOccurrenceSplit
end LeanTrominoes

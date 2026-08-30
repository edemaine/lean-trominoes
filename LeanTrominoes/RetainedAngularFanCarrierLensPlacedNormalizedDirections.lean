/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateGeometry
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirectionTranslation

/-! # Normalized fallbacks in placed carrier lenses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxRecDepth 10000

/-- Translation of one oriented canonical lens route to its carrier origin. -/
def carrierLensPlacedRoute
    (origin : Cell)
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (localClauseIndex literalIndex : Nat) : List Cell :=
  translatePolyline origin
    (carrierLensTemplateRoute geometry.horizontal geometry.span
      localClauseIndex literalIndex)

/-- Placing a carrier lens translates every complete fallback route and
therefore preserves the canonical normalized carrier record word. -/
theorem carrierLensPlacedRoute_normalized_fallback_directions
    (origin : Cell)
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              localClauseIndex literalIndex).splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (carrierLensPlacedRoute origin geometry
                localClauseIndex literalIndex))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData geometry.horizontal geometry.span
                localClauseIndex literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        geometry localClauseIndex literalIndex slot := by
  calc
    _ = Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            ((CarrierFallbackRouteTailRecords.routeKind
                localClauseIndex literalIndex).splicedOwnFigure7Route
              (scalePolyline retainedAngularFanSourceClearanceFactor
                (carrierLensTemplateRoute geometry.horizontal geometry.span
                  localClauseIndex literalIndex))
              (scaleRetainedTerminalData
                retainedAngularFanSourceClearanceFactor
                (carrierLensRouteTerminalData geometry.horizontal
                  geometry.span localClauseIndex literalIndex))
              slot)) := by
      simpa [carrierLensPlacedRoute] using
        (CarrierFallbackRouteTailRecords.routeKind
          localClauseIndex literalIndex).scaledSplicedOwnFigure7Route_translate_normalized_directions
            origin
            (carrierLensTemplateRoute geometry.horizontal geometry.span
              localClauseIndex literalIndex)
            (carrierLensRouteTerminalData geometry.horizontal geometry.span
              localClauseIndex literalIndex)
            slot retainedAngularFanSourceClearanceFactor_pos
            (carrierLensTemplateRoute_length geometry
              localClauseIndex literalIndex)
            (carrierLensTemplateRoute_carrier_classified geometry spanLarge
              localClauseIndex literalIndex)
            (carrierLensTemplateRoute_orthogonal geometry spanLarge
              localClauseIndex literalIndex)
            (carrierLensRouteTerminalData_positive geometry spanLarge
              localClauseIndex literalIndex)
            (carrierLensRouteFallback_valid geometry spanLarge
              localClauseIndex literalIndex)
    _ = _ := carrierLensTemplateRoute_normalized_fallback_directions
      geometry spanLarge localClauseIndex literalIndex slot

end PeriodicEightOccurrenceSplit
end LeanTrominoes

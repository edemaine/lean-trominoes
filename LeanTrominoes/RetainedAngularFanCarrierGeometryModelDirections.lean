/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierRouteNormalizedDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledPrefixGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledTerminalGeometry

/-! # Named finite-geometry carrier direction certificates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- The normalized compiler equality for a route in finite carrier geometry
coordinates. -/
structure FinalCarrierGeometryModelDirections
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell) : Prop where
  directions :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              localClauseIndex literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData geometry.horizontal geometry.span
                localClauseIndex literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        geometry localClauseIndex literalIndex slot

/-- Length, classification, orthogonality, and prefix certificates prove the
named finite-geometry compiler equality. -/
theorem finalCarrierGeometryModelDirections_of_evidence
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (routeLength : 2 ≤ route.length)
    (routeClassified : FinalCarrierGeometryClassification route geometry
      localClauseIndex literalIndex)
    (routeOrthogonal : OrthogonalPolyline route)
    (routePrefixDirections : FinalCarrierGeometryPrefixDirections route
      geometry localClauseIndex literalIndex) :
    FinalCarrierGeometryModelDirections geometry localClauseIndex literalIndex
      slot route :=
  ⟨carrierRoute_normalized_fallback_directions_eq geometry spanLarge
    localClauseIndex literalIndex slot route routeLength
    routeClassified.classified routeOrthogonal
    routePrefixDirections.prefixDirections⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes

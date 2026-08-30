/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierRouteNormalizedDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry

/-! # Directional extensionality for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- A final carrier source route may expose its prefix using the actual
integral endpoint span; the finite geometry equality transports that word to
the canonical compiler model before normalization. -/
theorem finalCarrierRoute_normalized_fallback_directions_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt
        source taggedLink nextSlice).span)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (routeLength : 2 ≤ route.length)
    (routeClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex)))
    (routeOrthogonal : OrthogonalPolyline route)
    (routePrefixDirections :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) =
        Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections
            taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                taggedLink.1.second))
            (if taggedLink.2 then 0 else 1) literalIndex)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              (finalCarrierLocalClauseIndex taggedLink)
              literalIndex).splicedOwnFigure7Route
            route
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData
                (finalCarrierRouteGeometryAt
                  source taggedLink nextSlice).horizontal
                (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
                (finalCarrierLocalClauseIndex taggedLink) literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (finalCarrierRouteGeometryAt source taggedLink nextSlice)
        (finalCarrierLocalClauseIndex taggedLink) literalIndex slot := by
  have routeClassifiedGeometry := routeClassified
  rw [carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    source taggedLink nextSlice literalIndex] at routeClassifiedGeometry
  apply carrierRoute_normalized_fallback_directions_eq
    (finalCarrierRouteGeometryAt source taggedLink nextSlice)
    spanLarge (finalCarrierLocalClauseIndex taggedLink) literalIndex slot route
    routeLength routeClassifiedGeometry routeOrthogonal
  exact routePrefixDirections.trans
    (repeatCarrierLensRoutePrefixDirections_finalCarrierRouteGeometryAt
      source taggedLink nextSlice literalIndex)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

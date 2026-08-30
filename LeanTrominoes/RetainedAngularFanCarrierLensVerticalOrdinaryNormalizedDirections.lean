/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensHorizontalOrdinaryNormalizedDirections

/-! # Normalized ordinary fallbacks in the vertical carrier lens -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

set_option maxRecDepth 10000

/-- Quarter-turn of the upper-right horizontal lens route toward north. -/
def verticalEqualityLensUpperRightRoute (span : Int) : List Cell :=
  [(0, 3), (2, 3), (2, span), (0, span)]

/-- Quarter-turn of the lower-left horizontal lens route toward north. -/
def verticalEqualityLensLowerLeftRoute : List Cell :=
  [(0, 6), (-1, 6), (-1, 0), (0, 0)]

/-- The upper-right route of a vertical carrier lens has the canonical
normalized ordinary-fallback direction word. -/
theorem verticalEqualityLensUpperRightRoute_normalized_fallback_directions
    (span : Nat)
    (spanLarge : 8 ≤ span)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (verticalEqualityLensUpperRightRoute span))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData false span 0 1))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections false span 0 1) ++
        retainedNormalizedFallbackFanSuffixDirections .ordinary
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData false span 0 1))
          slot := by
  let route := verticalEqualityLensUpperRightRoute (span : Int)
  let terminal := carrierLensRouteTerminalData false (span : Int) 0 1
  have classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal := by
    simp [route, terminal, carrierLensRouteTerminalData,
      verticalEqualityLensUpperRightRoute,
      PeriodicThreeSATThree.routeTerminalVector,
      gridPolylineSegments, retainedTerminalDirectionClassify,
      retainedRayClassify, terminalPort, compassLength,
      RetainedRay.terminalDirection, oppositePort, RetainedRay.length,
      Cell.sub]
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simp [route, verticalEqualityLensUpperRightRoute,
      LocalIncidenceDrawing.RouteIsSimple,
      gridPolylineSegments, GridSegment.InteriorsMeet,
      GridSegment.InteriorContains, GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween,
      GridSegment.IsHorizontal, GridSegment.IsVertical]
    omega
  have orthogonal : OrthogonalPolyline route := by
    simp [route, verticalEqualityLensUpperRightRoute,
      OrthogonalPolyline, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]
    omega
  have normalized :=
    scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
      route terminal slot .east 8 (1152 * (span - 3))
      retainedAngularFanSourceClearanceFactor_pos
      (by native_decide)
      (by simp [route, verticalEqualityLensUpperRightRoute])
      classified simple orthogonal
      (by simp [terminal, carrierLensRouteTerminalData])
      (by simp [terminal, carrierLensRouteTerminalData,
        retainedAngularFanSourceClearanceFactor_eq,
        scaleRetainedTerminalData])
      (by simp)
      (by omega)
      (by omega)
      (by
        rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
        simp [route, retainedFallbackSourcePrefix,
          retainedFallbackFanCenter,
          verticalEqualityLensUpperRightRoute,
          retainedAngularFanSourceClearanceFactor_eq,
          scalePolyline,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanTotalRefinement,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRoutingRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale]
        omega)
  rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
    at normalized
  have spanThree : 3 < span := by omega
  have spanThreeInt : (3 : Int) < span := by exact_mod_cast spanThree
  have spanNe : (3 : Int) ≠ span := ne_of_lt spanThreeInt
  simpa [route, terminal, carrierLensRoutePrefixDirections,
    verticalEqualityLensUpperRightRoute,
    Gadget.unitSubdivisionDirections,
    AxisDirection.segmentLength, AxisDirection.between,
    Cell.sub, spanThree, spanNe] using normalized

/-- The lower-left route of a vertical carrier lens has the canonical
normalized ordinary-fallback direction word. -/
theorem verticalEqualityLensLowerLeftRoute_normalized_fallback_directions
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              verticalEqualityLensLowerLeftRoute)
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData false 8 1 0))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections false 8 1 0) ++
        retainedNormalizedFallbackFanSuffixDirections .ordinary
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData false 8 1 0))
          slot := by
  let route := verticalEqualityLensLowerLeftRoute
  let terminal := carrierLensRouteTerminalData false 8 1 0
  have classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal := by
    native_decide
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    native_decide
  have orthogonal : OrthogonalPolyline route := by
    native_decide
  have normalized :=
    scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
      route terminal slot .west 4 6912
      retainedAngularFanSourceClearanceFactor_pos
      (by native_decide)
      (by native_decide)
      classified simple orthogonal
      (by native_decide)
      (by native_decide)
      (by simp)
      (by omega)
      (by omega)
      (by
        rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
        simp [route, retainedFallbackSourcePrefix,
          retainedFallbackFanCenter,
          verticalEqualityLensLowerLeftRoute,
          retainedAngularFanSourceClearanceFactor_eq,
          scalePolyline,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanTotalRefinement,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRoutingRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale])
  rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
    at normalized
  simpa [route, terminal, carrierLensRoutePrefixDirections,
    verticalEqualityLensLowerLeftRoute,
    Gadget.unitSubdivisionDirections,
    AxisDirection.segmentLength, AxisDirection.between,
    Cell.sub] using normalized

end PeriodicEightOccurrenceSplit
end LeanTrominoes

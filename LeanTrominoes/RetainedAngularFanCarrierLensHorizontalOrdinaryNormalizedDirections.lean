/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalData
import LeanTrominoes.RetainedAngularFanFallbackCardinalTangentNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData

/-! # Normalized ordinary fallbacks in the horizontal carrier lens -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxRecDepth 10000

/-- The upper-right route of a horizontal carrier lens has the canonical
normalized ordinary-fallback direction word. -/
theorem horizontalEqualityLensUpperRightRoute_normalized_fallback_directions
    (span : Nat)
    (spanLarge : 8 ≤ span)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (horizontalEqualityLensUpperRightRoute span))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData true span 0 1))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections true span 0 1) ++
        retainedNormalizedFallbackFanSuffixDirections .ordinary
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData true span 0 1))
          slot := by
  let route := horizontalEqualityLensUpperRightRoute (span : Int)
  let terminal := carrierLensRouteTerminalData true (span : Int) 0 1
  have classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal := by
    simp [route, terminal, carrierLensRouteTerminalData,
      horizontalEqualityLensUpperRightRoute,
      PeriodicThreeSATThree.routeTerminalVector,
      gridPolylineSegments, retainedTerminalDirectionClassify,
      retainedRayClassify, terminalPort, compassLength,
      RetainedRay.terminalDirection, oppositePort, RetainedRay.length,
      Cell.sub]
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simp [route, horizontalEqualityLensUpperRightRoute,
      LocalIncidenceDrawing.RouteIsSimple,
      gridPolylineSegments, GridSegment.InteriorsMeet,
      GridSegment.InteriorContains, GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween,
      GridSegment.IsHorizontal, GridSegment.IsVertical]
    omega
  have orthogonal : OrthogonalPolyline route := by
    simp [route, horizontalEqualityLensUpperRightRoute,
      OrthogonalPolyline,
      GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]
    omega
  have normalized :=
    scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
      route terminal slot .north 8 (1152 * (span - 3))
      retainedAngularFanSourceClearanceFactor_pos
      (by native_decide)
      (by simp [route, horizontalEqualityLensUpperRightRoute])
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
          horizontalEqualityLensUpperRightRoute,
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
  simpa [route, terminal, carrierLensRoutePrefixDirections,
    horizontalEqualityLensUpperRightRoute,
    Gadget.unitSubdivisionDirections,
    AxisDirection.segmentLength, AxisDirection.between,
    Cell.sub, spanThree] using normalized

/-- The lower-left route of a horizontal carrier lens has the canonical
normalized ordinary-fallback direction word. -/
theorem horizontalEqualityLensLowerLeftRoute_normalized_fallback_directions
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              horizontalEqualityLensLowerLeftRoute)
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData true 8 1 0))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections true 8 1 0) ++
        retainedNormalizedFallbackFanSuffixDirections .ordinary
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData true 8 1 0))
          slot := by
  let route := horizontalEqualityLensLowerLeftRoute
  let terminal := carrierLensRouteTerminalData true 8 1 0
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
      route terminal slot .south 4 6912
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
          horizontalEqualityLensLowerLeftRoute,
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
    horizontalEqualityLensLowerLeftRoute,
    Gadget.unitSubdivisionDirections,
    AxisDirection.segmentLength, AxisDirection.between,
    Cell.sub] using normalized

end PeriodicEightOccurrenceSplit
end LeanTrominoes

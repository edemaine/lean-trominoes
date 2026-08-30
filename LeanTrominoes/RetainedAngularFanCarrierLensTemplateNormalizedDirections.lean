/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanCarrierLensVerticalOrdinaryNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackSingletonNormalizedDirections

/-! # Normalized fallbacks in the complete carrier-lens template -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxRecDepth 10000

/-- The east-facing equality-lens route table, or its north-facing
quarter-turn, before placing the lens at its carrier endpoint. -/
def carrierLensTemplateRoute
    (horizontal : Bool) (span : Int)
    (localClauseIndex literalIndex : Nat) : List Cell :=
  if horizontal then
    horizontalEqualityLensRoutes span localClauseIndex literalIndex
  else
    (horizontalEqualityLensRoutes span localClauseIndex literalIndex).map
      AxisDirection.north.orientPoint

/-- The upper-left straight route has a singleton retained prefix, so its
escaped fallback has the canonical normalized word. -/
theorem carrierLensTemplateRoute_upperLeft_normalized_fallback_directions
    (horizontal : Bool)
    (span : Nat)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.escaped.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (carrierLensTemplateRoute horizontal span 0 0))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData horizontal span 0 0))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections horizontal span 0 0) ++
        retainedNormalizedFallbackFanSuffixDirections .escaped
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData horizontal span 0 0))
          slot := by
  cases horizontal
  ·
    have normalized :=
      RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
        .escaped
        (carrierLensTemplateRoute false 8 0 0)
        (carrierLensRouteTerminalData false 8 0 0) slot
        retainedAngularFanSourceClearanceFactor_pos
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by
          simpa [RetainedFallbackFanKind.Valid,
            retainedAngularFanSourceClearanceFactor_eq] using
            retainedTerminalFanOuterSourceEscape_fits_scale_four
              (carrierLensRouteTerminalData false 8 0 0)
              (by native_decide))
        (by native_decide)
    rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
      at normalized
    simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections,
      Gadget.unitSubdivisionDirections] using normalized
  ·
    have normalized :=
      RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
        .escaped
        (carrierLensTemplateRoute true 8 0 0)
        (carrierLensRouteTerminalData true 8 0 0) slot
        retainedAngularFanSourceClearanceFactor_pos
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by native_decide)
        (by
          simpa [RetainedFallbackFanKind.Valid,
            retainedAngularFanSourceClearanceFactor_eq] using
            retainedTerminalFanOuterSourceEscape_fits_scale_four
              (carrierLensRouteTerminalData true 8 0 0)
              (by native_decide))
        (by native_decide)
    rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
      at normalized
    simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections,
      Gadget.unitSubdivisionDirections] using normalized

/-- The lower-right straight route also has a singleton retained prefix, so
its escaped fallback has the canonical normalized word. -/
theorem carrierLensTemplateRoute_lowerRight_normalized_fallback_directions
    (horizontal : Bool)
    (span : Nat)
    (spanLarge : 8 ≤ span)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.escaped.splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (carrierLensTemplateRoute horizontal span 1 1))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData horizontal span 1 1))
            slot)) =
      Gadget.repeatDirections 1152
          (carrierLensRoutePrefixDirections horizontal span 1 1) ++
        retainedNormalizedFallbackFanSuffixDirections .escaped
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData horizontal span 1 1))
          slot := by
  have spanSixNat : 6 < span := by omega
  have spanSix : (6 : Int) < span := by exact_mod_cast spanSixNat
  have spanNotLtSix : ¬(span : Int) < 6 := by omega
  have spanDiffNeZero : (span : Int) - 6 ≠ 0 := by omega
  cases horizontal
  ·
    have terminalPositive :
        0 < (carrierLensRouteTerminalData false span 1 1).2 := by
      simp [carrierLensRouteTerminalData]
      omega
    have normalized :=
      RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
        .escaped
        (carrierLensTemplateRoute false span 1 1)
        (carrierLensRouteTerminalData false span 1 1) slot
        retainedAngularFanSourceClearanceFactor_pos
        (by simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
          horizontalEqualityLensLowerRightRoute])
        (by
          change retainedTerminalDirectionClassify
              (PeriodicThreeSATThree.routeTerminalVector
                (carrierLensTemplateRoute false span 1 1)) =
            some (.compass .north, ((span : Int) - 6).toNat)
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute,
            PeriodicThreeSATThree.routeTerminalVector,
            gridPolylineSegments, retainedTerminalDirectionClassify,
            retainedRayClassify, terminalPort, compassLength,
            RetainedRay.terminalDirection, oppositePort,
            RetainedRay.length, AxisDirection.orientPoint,
            Cell.sub, spanSix, spanNotLtSix])
        (by
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute,
            LocalIncidenceDrawing.RouteIsSimple, gridPolylineSegments,
            GridSegment.InteriorsMeet, GridSegment.InteriorContains,
            GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            AxisDirection.orientPoint]
          omega)
        (by
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute, OrthogonalPolyline,
            GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
            GridSegment.IsVertical, AxisDirection.orientPoint]
          omega)
        terminalPositive
        (by
          simpa [RetainedFallbackFanKind.Valid,
            retainedAngularFanSourceClearanceFactor_eq] using
            retainedTerminalFanOuterSourceEscape_fits_scale_four
              (carrierLensRouteTerminalData false span 1 1)
              terminalPositive)
        (by simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
          horizontalEqualityLensLowerRightRoute])
    rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
      at normalized
    simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensLowerRightRoute,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections,
      Gadget.unitSubdivisionDirections] using normalized
  ·
    have terminalPositive :
        0 < (carrierLensRouteTerminalData true span 1 1).2 := by
      simp [carrierLensRouteTerminalData]
      omega
    have normalized :=
      RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_singleton_normalized_directions
        .escaped
        (carrierLensTemplateRoute true span 1 1)
        (carrierLensRouteTerminalData true span 1 1) slot
        retainedAngularFanSourceClearanceFactor_pos
        (by simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
          horizontalEqualityLensLowerRightRoute])
        (by
          change retainedTerminalDirectionClassify
              (PeriodicThreeSATThree.routeTerminalVector
                (carrierLensTemplateRoute true span 1 1)) =
            some (.compass .west, ((span : Int) - 6).toNat)
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute,
            PeriodicThreeSATThree.routeTerminalVector,
            gridPolylineSegments, retainedTerminalDirectionClassify,
            retainedRayClassify, terminalPort, compassLength,
            RetainedRay.terminalDirection, oppositePort,
            RetainedRay.length, Cell.sub, spanNotLtSix,
            spanDiffNeZero])
        (by
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute,
            LocalIncidenceDrawing.RouteIsSimple, gridPolylineSegments,
            GridSegment.InteriorsMeet, GridSegment.InteriorContains,
            GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical]
          omega)
        (by
          simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute, OrthogonalPolyline,
            GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
            GridSegment.IsVertical]
          omega)
        terminalPositive
        (by
          simpa [RetainedFallbackFanKind.Valid,
            retainedAngularFanSourceClearanceFactor_eq] using
            retainedTerminalFanOuterSourceEscape_fits_scale_four
              (carrierLensRouteTerminalData true span 1 1)
              terminalPositive)
        (by simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
          horizontalEqualityLensLowerRightRoute])
    rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions]
      at normalized
    simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensLowerRightRoute,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections,
      Gadget.unitSubdivisionDirections] using normalized

/-- Every route of either canonical carrier-lens orientation normalizes to
the exact mixed-policy word stored by the carrier record layer. -/
theorem carrierLensTemplateRoute_normalized_fallback_directions
    (geometry :
      CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((CarrierFallbackRouteTailRecords.routeKind
              localClauseIndex literalIndex).splicedOwnFigure7Route
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (carrierLensTemplateRoute geometry.horizontal geometry.span
                localClauseIndex literalIndex))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (carrierLensRouteTerminalData geometry.horizontal geometry.span
                localClauseIndex literalIndex))
            slot)) =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        geometry localClauseIndex literalIndex slot := by
  rcases geometry with ⟨horizontal, nextSlice, span⟩
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex
  · simpa [CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using carrierLensTemplateRoute_upperLeft_normalized_fallback_directions
        false span slot
  · simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperRightRoute,
      verticalEqualityLensUpperRightRoute, AxisDirection.orientPoint,
      CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using verticalEqualityLensUpperRightRoute_normalized_fallback_directions
        span spanLarge slot
  · simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensLowerLeftRoute,
      verticalEqualityLensLowerLeftRoute, AxisDirection.orientPoint,
      CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections]
      using verticalEqualityLensLowerLeftRoute_normalized_fallback_directions
        slot
  · simpa [CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using carrierLensTemplateRoute_lowerRight_normalized_fallback_directions
        false span spanLarge slot
  · simpa [CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using carrierLensTemplateRoute_upperLeft_normalized_fallback_directions
        true span slot
  · simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperRightRoute,
      CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using horizontalEqualityLensUpperRightRoute_normalized_fallback_directions
        span spanLarge slot
  · simpa [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensLowerLeftRoute,
      CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections,
      carrierLensRouteTerminalData, carrierLensRoutePrefixDirections]
      using horizontalEqualityLensLowerLeftRoute_normalized_fallback_directions
        slot
  · simpa [CarrierNormalizedFallbackRouteTailRecords.routeDirections,
      CarrierFallbackRouteTailRecords.routeQuery,
      CarrierFallbackRouteTailRecords.routeKind,
      NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections]
      using carrierLensTemplateRoute_lowerRight_normalized_fallback_directions
        true span spanLarge slot

end PeriodicEightOccurrenceSplit
end LeanTrominoes

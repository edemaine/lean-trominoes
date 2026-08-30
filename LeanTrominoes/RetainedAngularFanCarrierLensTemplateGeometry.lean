/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateClassification
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateNormalizedDirections

/-! # Geometry certificates for the canonical carrier-lens template -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxRecDepth 10000

/-- The lightweight explicit route table agrees with the canonical
horizontal-template-or-quarter-turn presentation. -/
theorem carrierLensRawTemplateRoute_eq
    (horizontal : Bool)
    (span : Nat)
    (localClauseIndex literalIndex : Fin 2) :
    carrierLensRawTemplateRoute horizontal span
        localClauseIndex literalIndex =
      carrierLensTemplateRoute horizontal span
        localClauseIndex literalIndex := by
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex <;>
    simp [carrierLensRawTemplateRoute, carrierLensTemplateRoute,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      AxisDirection.orientPoint]

/-- The lightweight template terminal table is the public carrier metadata
table at every one of the four route positions. -/
theorem carrierLensTemplateRoute_carrier_classified
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensTemplateRoute geometry.horizontal geometry.span
            localClauseIndex literalIndex)) =
      some (carrierLensRouteTerminalData geometry.horizontal geometry.span
        localClauseIndex literalIndex) := by
  rw [← carrierLensRawTemplateRoute_eq geometry.horizontal geometry.span
    localClauseIndex literalIndex]
  have terminalEq :
      carrierLensTemplateTerminalData geometry.horizontal geometry.span
          localClauseIndex literalIndex =
        carrierLensRouteTerminalData geometry.horizontal geometry.span
          localClauseIndex literalIndex := by
    fin_cases localClauseIndex <;> fin_cases literalIndex <;> rfl
  rw [← terminalEq]
  exact carrierLensTemplateRoute_classified geometry.horizontal geometry.span
    spanLarge localClauseIndex literalIndex

theorem carrierLensTemplateRoute_length
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (localClauseIndex literalIndex : Fin 2) :
    2 ≤ (carrierLensTemplateRoute geometry.horizontal geometry.span
      localClauseIndex literalIndex).length := by
  rcases geometry with ⟨horizontal, nextSlice, span⟩
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex <;>
    simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]

theorem carrierLensTemplateRoute_orthogonal
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    OrthogonalPolyline
      (carrierLensTemplateRoute geometry.horizontal geometry.span
        localClauseIndex literalIndex) := by
  rcases geometry with ⟨horizontal, nextSlice, span⟩
  change 8 ≤ span at spanLarge
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex <;>
    simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, AxisDirection.orientPoint] <;>
    omega

theorem carrierLensRouteTerminalData_positive
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    0 < (carrierLensRouteTerminalData geometry.horizontal geometry.span
      localClauseIndex literalIndex).2 := by
  rcases geometry with ⟨horizontal, nextSlice, span⟩
  change 8 ≤ span at spanLarge
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex <;>
    simp [carrierLensRouteTerminalData] <;>
    omega

theorem carrierLensRouteFallback_valid
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    (CarrierFallbackRouteTailRecords.routeKind
        localClauseIndex literalIndex).Valid
      (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData geometry.horizontal geometry.span
          localClauseIndex literalIndex)) := by
  have terminalPositive := carrierLensRouteTerminalData_positive
    geometry spanLarge localClauseIndex literalIndex
  fin_cases localClauseIndex <;> fin_cases literalIndex
  · simpa [CarrierFallbackRouteTailRecords.routeKind,
      RetainedFallbackFanKind.Valid,
      retainedAngularFanSourceClearanceFactor_eq] using
      retainedTerminalFanOuterSourceEscape_fits_scale_four
        (carrierLensRouteTerminalData geometry.horizontal geometry.span 0 0)
        terminalPositive
  · simp [CarrierFallbackRouteTailRecords.routeKind,
      RetainedFallbackFanKind.Valid]
  · simp [CarrierFallbackRouteTailRecords.routeKind,
      RetainedFallbackFanKind.Valid]
  · simpa [CarrierFallbackRouteTailRecords.routeKind,
      RetainedFallbackFanKind.Valid,
      retainedAngularFanSourceClearanceFactor_eq] using
      retainedTerminalFanOuterSourceEscape_fits_scale_four
        (carrierLensRouteTerminalData geometry.horizontal geometry.span 1 1)
        terminalPositive

end PeriodicEightOccurrenceSplit
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateGeometry
import LeanTrominoes.RetainedAngularFanFallbackSplicedRouteValidity
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData

/-! # Unit steps of normalized carrier fallback models -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Packaged source-route evidence and a valid finite carrier geometry make
the corresponding normalized fallback model a unit-step route. -/
theorem FinalCarrierScaledRouteEvidence.normalizedCarrierRouteUnitSteps
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2)
    (slot : RetainedTerminalSlot)
    (route : List Cell)
    (prefixDirections : List AxisDirection)
    (evidence : FinalCarrierScaledRouteEvidence route
      (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData geometry.horizontal geometry.span
          localClauseIndex literalIndex))
      prefixDirections) :
    (AxisDirection.normalizeOrthogonalPolyline
      ((CarrierFallbackRouteTailRecords.routeKind
          localClauseIndex literalIndex).splicedOwnFigure7Route
        route
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (carrierLensRouteTerminalData geometry.horizontal geometry.span
            localClauseIndex literalIndex))
        slot)).IsChain AxisDirection.IsUnitAxisStep := by
  let terminal := scaleRetainedTerminalData
    retainedAngularFanSourceClearanceFactor
    (carrierLensRouteTerminalData geometry.horizontal geometry.span
      localClauseIndex literalIndex)
  let kind := CarrierFallbackRouteTailRecords.routeKind
    localClauseIndex literalIndex
  have terminalPositive : 0 < terminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      (carrierLensRouteTerminalData_positive geometry spanLarge
        localClauseIndex literalIndex)
  have kindValid : kind.Valid terminal := by
    exact carrierLensRouteFallback_valid geometry spanLarge
      localClauseIndex literalIndex
  have splicedValid := kind.splicedOwnFigure7Route_valid
    route terminal slot evidence.routeLength evidence.routeClassified
    evidence.routeOrthogonal terminalPositive kindValid
  exact AxisDirection.normalizeOrthogonalPolyline_unitSteps
    splicedValid.1 splicedValid.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationEndpointContacts
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationHaloBounds

/-!
# Ribbon-ready polarity normalization

This file combines the independently transported halo and endpoint-contact
certificates into the complete source interface consumed by the planar 3DM
ribbon construction.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Polarity normalization preserves the complete halo-bounded ribbon-ready
incidence-presentation interface, provided the source routes use unit steps. -/
def haloBoundedRibbonReadyPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes) where
  toHaloBoundedContinuousPlanarIncidencePresentation :=
    haloBoundedContinuousPlanarPresentation
      presentation.toHaloBoundedContinuousPlanarIncidencePresentation
  endpointContacts :=
    incidenceDrawing_routePointsMeetOnlyAtEndpoints
      presentation sourceUnitSteps

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

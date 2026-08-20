/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentation

/-! # Route projection of the semantic horizontal presentation -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The typed normalized presentation stores the doubled routed family named
by the proof-free semantic data. -/
theorem horizontalSemanticNormalizedPlanarPresentation_routes
    (source : PeriodicCNF Nat) :
    (horizontalSemanticNormalizedPlanarPresentation source).routes =
      PositionedPeriodicCNF.scaleIncidenceRoutes 2
        (horizontalSemanticRoutedRoutes source) := by
  simp only [
    horizontalSemanticNormalizedPlanarPresentation,
    horizontalSemanticNormalizedRibbonReadyPresentation,
    PeriodicPlanarOneInThreeToThreeDM.normalizedRibbonReadyIncidencePresentation,
    PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation.anchorNormalize,
    PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation.anchorNormalize,
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation.anchorNormalize,
    PositionedPeriodicCNF.PlanarIncidencePresentation.anchorNormalize,
    PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation.scaleTwo,
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation.scale,
    horizontalSemanticRoutedRibbonReadyPresentation,
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.haloBoundedRibbonReadyPresentation,
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.haloBoundedContinuousPlanarPresentation,
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.continuousPlanarPresentation,
    horizontalSemanticRoutedRoutes,
    horizontalRoutes]

end PeriodicCNFStripReduction
end LeanTrominoes

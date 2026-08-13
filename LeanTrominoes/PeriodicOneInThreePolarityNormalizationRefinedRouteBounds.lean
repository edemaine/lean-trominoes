/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalPlanarization
import LeanTrominoes.PositionedPeriodicCNFRibbonScaling
import LeanTrominoes.PositionedPeriodicCNFUnitSubdivisionRouteBounds

/-!
# Halo bounds for the refined polarity-normalization routes

The complete refined source routes are obtained by anchor normalization,
threefold scaling, and ordered unit subdivision.  The first two operations
preserve the rebased-route halo by exact transport; orthogonal convexity of
the halo handles the newly inserted subdivision points.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Package the complete refined route family as a continuously planar
incidence presentation. -/
def refinedContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement) := by
  let scaled := scaledSourcePresentation presentation
  let family := refinedRouteFamily presentation
  exact {
    routes := family.routes
    periodPositive := scaled.periodPositive
    compatible := family.isCompatible_of_reference
      scaled.periodPositive scaled.routes scaled.compatible
    orthogonal := family.isOrthogonal
    planar := (refinedRouteFamily_isContinuouslyPlanar presentation).1
    continuouslyPlanar :=
      refinedRouteFamily_isContinuouslyPlanar presentation
  }

@[simp]
theorem refinedContinuousPlanarPresentation_routes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (refinedContinuousPlanarPresentation presentation).routes =
      (refinedRouteFamily presentation).routes := by
  rfl

/-- Complete refined routes inherit the ordinary open rebased-route halo
from a halo-bounded source presentation. -/
theorem refinedRouteFamily_rebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (refinedContinuousPlanarPresentation
      presentation.toContinuousPlanarIncidencePresentation)
      |>.toPlanarIncidencePresentation
      |>.RebasedRoutePointsInExpandedSquare := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  let scaled :=
    presentation.anchorNormalize.toContinuousPlanarIncidencePresentation
      |>.scale refinementFactor_positive
  let refined := refinedContinuousPlanarPresentation continuous
  have scaledBounds :
      scaled.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquare := by
    exact
      (presentation.anchorNormalize
        |>.rebasedRoutePointsInExpandedSquare_scale
          refinementFactor_positive)
  exact
    scaled.toPlanarIncidencePresentation
      |>.rebasedRoutePointsInExpandedSquare_of_unitSubdivide
        refined.toPlanarIncidencePresentation
          (by intro clauseIndex literalIndex; rfl)
          scaledBounds

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

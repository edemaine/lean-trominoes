/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonCompatibility
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRibbonOrders
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteRadiusBounds

/-!
# Ribbon presentation boundary for the ordered retained Figure 9 endpoint

Complete route separation already proves continuous planarity and
endpoint-only route contacts for the final normalized drawing.  This module
packages those facts into the source interface consumed by ribbon thickening,
leaving explicit only the route-independent finite compatibility certificate
and the rebased-route halo bound.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 200000

local instance orderedRibbonPresentationVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (RetainedOrderedFixedEightOneInThreeVariable Variable) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Install the final normalized routes as a planar incidence presentation,
given the remaining route-independent finite compatibility certificate. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    PositionedPeriodicCNF.PlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source) where
  routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  periodPositive :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
      source
  compatible := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
      using compatible
  orthogonal := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isOrthogonal
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  planar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isPlanar
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty

/-- Upgrade the installed planar presentation to continuous planarity using
the completed global route-separation theorem. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source) where
  toPlanarIncidencePresentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty compatible
  continuouslyPlanar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).1

/-- The normalized composed route-radius certificate places every rebased
route point in the open one-period halo of the final incidence drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation_rebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty compatible)
      |>.RebasedRoutePointsInExpandedSquare := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty compatible
  apply presentation.rebasedRoutePointsInExpandedSquare_of_withinVariablePeriod
  apply presentation.rebasedRoutePointsWithinVariablePeriod_of_raw
  simpa [presentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation]
    using
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_withinVariablePeriod
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- Add the now-verified rebased-route halo bound to the continuously planar
final route family. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source) where
  toContinuousPlanarIncidencePresentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedContinuousPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty compatible
  rebasedRoutePointsInside := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedContinuousPlanarIncidencePresentation]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation_rebasedRoutePointsInExpandedSquare
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty compatible

/-- Promote the final normalized drawing to the complete halo-bounded,
ribbon-ready source interface once its remaining finite compatibility fact
is supplied. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedRibbonReadyIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source).HaloBoundedRibbonReadyIncidencePresentation
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source) := by
  refine
    @PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation.mk
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      orderedRibbonPresentationVariableDecidableEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedContinuousPlanarIncidencePresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty compatible)
      ?_
  ·
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedContinuousPlanarIncidencePresentation,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedContinuousPlanarIncidencePresentation,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).2

/-- Under the two residual finite-presentation facts, the concrete final
Figure 9 source presentation has compatible clockwise ribbon fans. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPresentation_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (compatible :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).IsCompatible
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase.incidenceGraph) :
    let presentation :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedRibbonReadyIncidencePresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty compatible
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedRibbonReadyIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty compatible
  apply
    @retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnits_sourceRibbonFansClockwiseCompatible
      Variable (inferInstance)
      orderedRibbonPresentationVariableDecidableEq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty presentation
  simp only [presentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedRibbonReadyIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedHaloBoundedContinuousPlanarIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedContinuousPlanarIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedPlanarIncidencePresentation]

end PeriodicOrthocrossing
end LeanTrominoes

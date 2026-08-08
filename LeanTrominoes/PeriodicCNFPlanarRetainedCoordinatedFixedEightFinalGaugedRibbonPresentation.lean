import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPresentation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteOrders

/-!
# Halo-bounded final gauged Figure 9 presentation

The completed Figure 9 routes already fit within one physical period of
their variable endpoints.  Final clause ordering preserves that radius
certificate, and the canonical variable gauge translates every route and
its variable center together.  This file carries the bound through those
last two representation changes and packages the unconditional final
gauged drawing as a halo-bounded ribbon-ready presentation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance finalGaugedRibbonPresentationVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The canonical variable gauge preserves the final clockwise occurrence
order at every degree-three variable. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes]
    using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).variableGaugeCanonicalIncidenceRoutes
          (placement :=
            retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
            source)

/-- The canonical variable gauge likewise preserves the final clockwise
literal order at every ternary clause. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_ternaryClauseRoutesInClockwiseOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInClockwiseOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes]
    using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwise_ternaryClauseRoutesInClockwiseOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).variableGaugeCanonicalIncidenceRoutes
          (placement :=
            retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
            source)

/-- The final clause sort preserves the binary-or-ternary promise. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
    using
      PositionedPeriodicCNF.orderClausesByRouteDirection_arityTwoOrThree
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
          source)

/-- The canonical variable gauge preserves the binary-or-ternary promise. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge]
    using
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).variableGauge
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
            source)

/-- Binary-or-ternary arity gives the final gauged width-three promise. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase.WidthAtMost 3 := by
  intro clause clauseMember
  rcases
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clause clauseMember with
    clauseArity | clauseArity
  · exact clauseArity.le.trans (by decide)
  · exact clauseArity.le

/-- The final stable clause sort preserves the one-period route-radius
certificate of the completed normalized Figure 9 drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes]
    using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_withinVariablePeriod
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).orderCanonicalRoutesByClauseDirection

/-- Canonical variable gauging translates route points and their variable
centers together, so the final compatible drawing retains the same
one-period route-radius certificate. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes]
    using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes_withinVariablePeriod
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).variableGaugeCanonicalIncidenceRoutes
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
            source)

/-- Every rebased route point of the unconditional final gauged planar
presentation lies in its open one-period halo. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation_rebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
      |>.RebasedRoutePointsInExpandedSquare := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  apply presentation.rebasedRoutePointsInExpandedSquare_of_withinVariablePeriod
  apply presentation.rebasedRoutePointsWithinVariablePeriod_of_raw
  simpa [presentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation]
    using
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes_withinVariablePeriod
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- The final continuously planar presentation together with its automatic
one-period halo bound. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedHaloBoundedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source) where
  toContinuousPlanarIncidencePresentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedContinuousPlanarIncidencePresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rebasedRoutePointsInside := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedContinuousPlanarIncidencePresentation]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation_rebasedRoutePointsInExpandedSquare
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty

/-- The final gauged source presentation satisfies every geometric promise
needed by the ribbon 3DM construction, with no residual hypotheses. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedHaloBoundedRibbonReadyIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).HaloBoundedRibbonReadyIncidencePresentation
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source) := by
  refine
    @PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation.mk
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      finalGaugedRibbonPresentationVariableDecidableEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedHaloBoundedContinuousPlanarIncidencePresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      ?_
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedHaloBoundedContinuousPlanarIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedContinuousPlanarIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
    using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).2

end PeriodicOrthocrossing
end LeanTrominoes

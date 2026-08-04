import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedClauseRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Ordered retained Figure 9 route orders supply ribbon source fans

The final normalized Figure 9 route family has both cyclic-order properties
required by the coordinated ribbon source fans.  This file combines those
properties and transports the variable-side certificate to the opaque
decidable equality used by the public endpoint.  Any halo-bounded ribbon-ready
presentation carrying exactly these routes therefore has compatible variable
and clause source fans.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The normalized variable-route order, transferred to an explicitly chosen
decidable equality on the final Figure 9 variables. -/
theorem
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_variableRoutesInOccurrenceOrderFor
    {Variable : Type*} [DecidableEq Variable]
    (finalDecEq :
      DecidableEq
        (RetainedOrderedFixedEightOneInThreeVariable Variable))
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      finalDecEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

/-- The final normalized Figure 9 routes simultaneously satisfy the variable
and clause cyclic-order premises of the ribbon source fans. -/
theorem
    retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_ribbonRouteOrders
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) ∧
      PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  constructor
  · exact
      retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_variableRoutesInOccurrenceOrderFor
        retainedOrderedFixedEightOneInThreeVariableDecidableEq
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- A halo-bounded ribbon-ready presentation using the final normalized
Figure 9 routes has coordinated clockwise variable and clause source fans. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnits_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    [finalDecEq :
      DecidableEq
        (RetainedOrderedFixedEightOneInThreeVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (presentation :
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).HaloBoundedRibbonReadyIncidencePresentation
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source))
    (routesEq :
      presentation.toPlanarIncidencePresentation.routes =
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) :
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  apply
    PeriodicPlanarOneInThreeToThreeDM.sourceRibbonFansClockwiseCompatible_of_routeOrders
      (presentation := presentation)
  · exact
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_widthAtMostThree
        source
  · have finalOccurrences :=
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_occurrencesAtMostThreeFor
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    unfold RetainedOrderedFixedEightOccurrencesAtMostThree at finalOccurrences
    exact
      PeriodicCNF.occurrencesAtMost_congr_beq
        retainedOrderedFixedEightOneInThreeVariableBEq
        (@instBEqOfDecidableEq
          (RetainedOrderedFixedEightOneInThreeVariable Variable)
          finalDecEq)
        retainedOrderedFixedEightOneInThreeVariableLawfulBEq
        (by infer_instance) 3
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase
        finalOccurrences
  · exact
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
        source
  · apply
      PeriodicPlanarOneInThreeToThreeDM.sourceVariableDirectionsInOccurrenceOrder_of_routes
        presentation.toPlanarIncidencePresentation
    rw [routesEq]
    exact
      retainedOrderedFixedEightComposedRawNormalizedIncidenceRoutes_variableRoutesInOccurrenceOrderFor
        finalDecEq
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · rw [routesEq]
    exact
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

end PeriodicOrthocrossing
end LeanTrominoes

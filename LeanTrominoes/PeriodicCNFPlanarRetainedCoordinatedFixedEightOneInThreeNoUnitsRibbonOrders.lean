/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightThreeDM
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsNormalizedRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRouteIsolation
import LeanTrominoes.PeriodicGridDrawingLoopErasureRouteOrders
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Coordinated retained route orders supply ribbon source fans

The final coordinated unit-free exact-one route family has both cyclic-order
properties required by the ribbon source fans.  Its degree-three variable
terminals follow occurrence order clockwise, while its ternary clauses leave
in the canonical order built into unit elimination.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The final coordinated route family leaves every ternary clause in the
canonical literal-index order supplied by unit elimination. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes]
    using
      PositionedPeriodicCNF.splicedRoutes_ternaryClauseRoutesInUnitEliminationOrder
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- The final coordinated route family simultaneously satisfies the variable
and clause cyclic-order premises of the ribbon source fans. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ribbonRouteOrders
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) ∧
      PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  constructor
  · exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- Final loop erasure preserves both cyclic route orders needed by the
ribbon source fans. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_ribbonRouteOrders
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) ∧
      PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rw [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_eq_normalize]
  apply
    PositionedPeriodicCNF.ribbonRouteOrders_normalizeOrthogonalIncidenceRoutes_of_endpointIsolation
  · exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ribbonRouteOrders
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_endpointIsolation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).1
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_endpointIsolation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2

/-- The coordinated variable-route order, transferred to an explicitly
chosen decidable equality on the generated endpoint variables. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrderFor
    {Variable : Type*} [DecidableEq Variable]
    (finalDecEq :
      DecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable))
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
      (Classical.decEq _) finalDecEq
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- A ribbon-ready presentation using the coordinated route family has
coordinated clockwise variable and clause source fans. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnits_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    [finalDecEq :
      DecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (presentation :
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).HaloBoundedRibbonReadyIncidencePresentation
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
            source))
    (routesEq :
      presentation.toPlanarIncidencePresentation.routes =
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) :
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  apply
    PeriodicPlanarOneInThreeToThreeDM.sourceRibbonFansClockwiseCompatible_of_routeOrders
      (presentation := presentation)
  · exact
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_widthAtMostThree
        source
  · exact
      retainedCoordinatedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
        finalDecEq source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source
  · apply
      PeriodicPlanarOneInThreeToThreeDM.sourceVariableDirectionsInOccurrenceOrder_of_routes
        presentation.toPlanarIncidencePresentation
    rw [routesEq]
    exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrderFor
        finalDecEq source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · rw [routesEq]
    exact
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

end PeriodicOrthocrossing
end LeanTrominoes

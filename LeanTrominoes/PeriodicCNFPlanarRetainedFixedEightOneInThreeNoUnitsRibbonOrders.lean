/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightThreeDM
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Retained fixed-eight route orders supply ribbon source fans

The final retained unit-free exact-one route family has both cyclic-order
properties needed by the coordinated ribbon source fans.  Its degree-three
variable terminals follow occurrence order clockwise, while its ternary
clauses leave in the canonical order built into unit elimination.

The paired route-order certificate, together with the already-proved
width-three, occurrence-three, and binary-or-ternary promises, supplies the
premises of the generic source-fan compatibility theorem once the remaining
halo-bounded ribbon-ready presentation is built.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Binary-or-ternary arity gives the final retained exact-one formula the
width-three bound expected by the ribbon source-fan construction. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase.WidthAtMost 3 := by
  intro clause clauseMember
  rcases
      retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source clause clauseMember with arity | arity
  · exact arity.le.trans (by decide)
  · exact arity.le

/-- The final retained unit-free route family leaves every ternary clause in
the canonical literal-index order supplied by unit elimination. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes]
    using
      PositionedPeriodicCNF.splicedRoutes_ternaryClauseRoutesInUnitEliminationOrder
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
        (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- The final retained route family simultaneously satisfies the variable
and clause cyclic-order premises of the coordinated ribbon source fans. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ribbonRouteOrders
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) ∧
      PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  constructor
  · exact
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

/-- The retained variable-route order, transferred to an explicitly chosen
decidable equality on the generated endpoint variables. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrderFor
    {Variable : Type*} [DecidableEq Variable]
    (finalDecEq :
      DecidableEq (RetainedFixedEightOneInThreeVariable Variable))
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (RetainedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (RetainedFixedEightOneInThreeVariable Variable)
      (Classical.decEq _) finalDecEq
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- A ribbon-ready presentation using the retained route family has
coordinated clockwise variable and clause source fans. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnits_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    [finalDecEq :
      DecidableEq (RetainedFixedEightOneInThreeVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (presentation :
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).HaloBoundedRibbonReadyIncidencePresentation
          (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source))
    (routesEq :
      presentation.toPlanarIncidencePresentation.routes =
        retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) :
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  apply
    PeriodicPlanarOneInThreeToThreeDM.sourceRibbonFansClockwiseCompatible_of_routeOrders
      (presentation := presentation)
  · exact
      retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_widthAtMostThree
        source
  · exact
      retainedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
        finalDecEq source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source
  · apply
      PeriodicPlanarOneInThreeToThreeDM.sourceVariableDirectionsInOccurrenceOrder_of_routes
        presentation.toPlanarIncidencePresentation
    rw [routesEq]
    exact
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrderFor
        finalDecEq source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · rw [routesEq]
    exact
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty

end PeriodicOrthocrossing
end LeanTrominoes

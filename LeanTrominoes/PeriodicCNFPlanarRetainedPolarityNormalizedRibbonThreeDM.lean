/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonFans
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDM

/-!
# Polarity-normalized retained Figure 9 reduction to planar periodic 3DM

The retained Figure 9 construction first supplies a complete ribbon-ready
exact-one incidence drawing.  Routed polarity normalization is then applied
to that drawing before the padded three-strand 3DM assembly.  This order makes
the endpoint-clear polarity convention an output theorem instead of an extra
hypothesis.
-/

noncomputable section

namespace LeanTrominoes

namespace PositionedPeriodicCNF

/-- A variable gauge changes only occurrence offsets, so it preserves
pairwise distinct protovariables within every positioned clause. -/
theorem AllAtomsNodup.variableGauge
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (distinct : source.AllAtomsNodup)
    (gauge : Variable → Cell) :
    (source.variableGauge gauge).AllAtomsNodup := by
  intro gaugedClause gaugedMember
  rcases List.mem_map.mp gaugedMember with
    ⟨sourceClause, sourceMember, rfl⟩
  have sourceDistinct := distinct sourceClause sourceMember
  unfold PositionedPeriodicClause.AtomsNodup at sourceDistinct ⊢
  simpa [PeriodicClause.variableGauge, List.map_map,
    Function.comp_def] using sourceDistinct

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance retainedPolarityNormalizedVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The final gauged Figure 9 formula still has distinct protovariables in
each clause. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).AllAtomsNodup := by
  unfold
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
  apply PositionedPeriodicCNF.AllAtomsNodup.variableGauge
  exact
    (PositionedPeriodicCNF.orderClausesByRouteDirection_allAtomsNodup_iff
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).2
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_allAtomsNodup
        source)

/-- The padded periodic 3DM instance obtained after routed polarity
normalization of the retained Figure 9 presentation. -/
noncomputable def
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicThreeDM :=
  PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routes

/-- The corrected composition has a concrete continuously planar
presentation, with no residual polarity hypothesis. -/
noncomputable def
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).ContinuousPlanarPresentation := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      presentation.unitSteps
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      presentation.variableRoutesInOccurrenceOrder
      presentation.ternaryClauseRoutesInClockwiseOrder

/-- The concrete corrected composition also exposes the finite checker's
open-halo endpoint bound. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).drawing.SegmentEndpointsInExpandedSquare := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation_endpointBounds
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      presentation.unitSteps
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      presentation.variableRoutesInOccurrenceOrder
      presentation.ternaryClauseRoutesInClockwiseOrder

/-- Distinct lifted routes in the concrete corrected composition stay
disjoint, including across distinct period translates. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_separated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).drawing.LiftedRoutesAvoidEachOther := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation_separated
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      presentation.unitSteps
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      presentation.variableRoutesInOccurrenceOrder
      presentation.ternaryClauseRoutesInClockwiseOrder

/-- Every stored route in the concrete corrected composition is simple. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ route ∈
        (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation_routesSimple
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      presentation.unitSteps
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      presentation.variableRoutesInOccurrenceOrder
      presentation.ternaryClauseRoutesInClockwiseOrder

/-- The polarity-normalized padded target preserves the promised degree-two
or degree-three incidence bound. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).DegreeTwoOrThree := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_degreeTwoOrThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      presentation.routes
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Routed polarity normalization and padded 3DM preserve satisfiability of
the original periodic CNF exactly. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).Satisfiable ↔ source.Satisfiable := by
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have graphIff :
      (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).GraphHasOrientation ↔
      PeriodicOneInThree.Satisfiable
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase := by
    simpa [
      retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem,
      presentation] using
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_graphHasOrientation_iff
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        presentation.routes
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).occurrencesAtMostThree
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation _).trans
      (graphIff.trans
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_satisfiable_iff
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).trans
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff
            source sourceLocal sourceWidth sourceOccurrences)))

end PeriodicOrthocrossing
end LeanTrominoes

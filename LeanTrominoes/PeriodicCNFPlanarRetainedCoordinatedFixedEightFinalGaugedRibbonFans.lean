import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonPresentation

/-!
# Clockwise ribbon fans for the final gauged Figure 9 presentation

This module closes the combinatorial side conditions of the ribbon source at
the final canonically gauged endpoint.  Named proposition-level interfaces
keep the deeply nested reduction-variable equality out of downstream
normalization.
-/

namespace LeanTrominoes

namespace PositionedPeriodicCNF

/-- A ribbon-ready source presentation carrying both cyclic route-order
certificates required by its finite endpoint fans. -/
structure ClockwiseOrderedHaloBoundedRibbonReadyIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    extends HaloBoundedRibbonReadyIncidencePresentation source placement where
  unitSteps :
    (incidenceDrawing source placement routes).HasUnitSteps
  variableRoutesInOccurrenceOrder :
    source.VariableRoutesInOccurrenceOrder routes
  ternaryClauseRoutesInClockwiseOrder :
    source.TernaryClauseRoutesInClockwiseOrder routes

namespace ClockwiseOrderedHaloBoundedRibbonReadyIncidencePresentation

/-- The two stored cyclic route orders discharge every coordinated source-fan
table lookup. -/
theorem sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      ClockwiseOrderedHaloBoundedRibbonReadyIncidencePresentation
        source placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  apply
    PeriodicPlanarOneInThreeToThreeDM.sourceRibbonFansClockwiseCompatible_of_clockwiseRouteOrders
      presentation.toHaloBoundedRibbonReadyIncidencePresentation
      width occurrences arity
  · exact
      PeriodicPlanarOneInThreeToThreeDM.sourceVariableDirectionsInOccurrenceOrder_of_routes
        presentation.toPlanarIncidencePresentation
        presentation.variableRoutesInOccurrenceOrder
  · exact presentation.ternaryClauseRoutesInClockwiseOrder

end ClockwiseOrderedHaloBoundedRibbonReadyIncidencePresentation
end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

set_option maxHeartbeats 1000000

local instance finalGaugedRibbonFansVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Named Boolean equality definitionally matching the equality used by the
final gauged presentation. -/
@[reducible] def finalGaugedRibbonFansVariableBEq
    {Variable : Type*} [DecidableEq Variable] :
    BEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  @instBEqOfDecidableEq
    (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    finalGaugedRibbonFansVariableDecidableEq

/-- Lawfulness of the named final-presentation Boolean equality. -/
opaque finalGaugedRibbonFansVariableLawfulBEq
    {Variable : Type*} [DecidableEq Variable] :
    @LawfulBEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      finalGaugedRibbonFansVariableBEq := by
  unfold finalGaugedRibbonFansVariableBEq
  infer_instance

/-- Proof-carrying occurrence-three interface indexed only by the original
source data.  This keeps the expanded final formula out of downstream theorem
headers. -/
structure RetainedOrderedFixedEightFinalGaugedOccurrencesCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : Prop where
  occurrencesAtMostThree :
    @PeriodicCNF.OccurrencesAtMost
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      finalGaugedRibbonFansVariableBEq
      finalGaugedRibbonFansVariableLawfulBEq 3
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase

/-- Stable clause ordering and canonical variable gauging preserve the
occurrence-three promise of the completed Figure 9 formula. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    RetainedOrderedFixedEightFinalGaugedOccurrencesCertificate
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty := by
  constructor
  have rawOccurrencesNamed :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_occurrencesAtMostThreeFor
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold RetainedOrderedFixedEightOccurrencesAtMostThree at rawOccurrencesNamed
  have rawOccurrences :
      @PeriodicCNF.OccurrencesAtMost
        (RetainedOrderedFixedEightOneInThreeVariable Variable)
        finalGaugedRibbonFansVariableBEq
        finalGaugedRibbonFansVariableLawfulBEq 3
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      retainedOrderedFixedEightOneInThreeVariableBEq
      finalGaugedRibbonFansVariableBEq
      retainedOrderedFixedEightOneInThreeVariableLawfulBEq
      finalGaugedRibbonFansVariableLawfulBEq 3
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase
      rawOccurrencesNamed
  have orderedOccurrences :
      @PeriodicCNF.OccurrencesAtMost
        (RetainedOrderedFixedEightOneInThreeVariable Variable)
        finalGaugedRibbonFansVariableBEq
        finalGaugedRibbonFansVariableLawfulBEq 3
        (PositionedPeriodicCNF.orderClausesByRouteDirection
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)).erase :=
    (@PositionedPeriodicCNF.orderClausesByRouteDirection_occurrencesAtMost_iff
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      finalGaugedRibbonFansVariableBEq
      finalGaugedRibbonFansVariableLawfulBEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      3).2 rawOccurrences
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula,
    PositionedPeriodicCNF.erase_variableGauge]
    using
      (@PeriodicCNF.OccurrencesAtMost.variableGauge
        (RetainedOrderedFixedEightOneInThreeVariable Variable)
        finalGaugedRibbonFansVariableBEq
        finalGaugedRibbonFansVariableLawfulBEq
        (PositionedPeriodicCNF.orderClausesByRouteDirection
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)).erase
        3 orderedOccurrences
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source))

/-- The final geometric and cyclic-order certificates, assembled with the
canonical route family as an explicit structure field. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.ClockwiseOrderedHaloBoundedRibbonReadyIncidencePresentation
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source) where
  routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  periodPositive :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_pos
      source
  compatible := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isCompatible
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  orthogonal := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isOrthogonal
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  planar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).1.1
  continuouslyPlanar := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).1
  rebasedRoutePointsInside := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation_rebasedRoutePointsInExpandedSquare
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  endpointContacts := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).2
  unitSteps := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing]
      using
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_hasUnitSteps
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
  variableRoutesInOccurrenceOrder :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  ternaryClauseRoutesInClockwiseOrder :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_ternaryClauseRoutesInClockwiseOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

/-- Proof-carrying interface for the complete clockwise source-fan condition
at the final gauged endpoint. -/
structure RetainedOrderedFixedEightFinalGaugedRibbonFansCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : Prop where
  clockwiseCompatible :
    PeriodicPlanarOneInThreeToThreeDM.SourceRibbonFansClockwiseCompatible
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).toPlanarIncidencePresentation

/-- The unconditional final gauged presentation has clockwise-compatible
variable and clause ribbon fans. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPresentation_sourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    RetainedOrderedFixedEightFinalGaugedRibbonFansCertificate
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty := by
  constructor
  let presentation :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    presentation.sourceRibbonFansClockwiseCompatible
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_widthAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_occurrencesAtMostThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).occurrencesAtMostThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDM
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousDrawingBridge

/-! # Coordinated-routing witness behind the polarity-normalized drawing -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicPlanarOneInThreeToThreeDM

/-- Proof package identifying a grid drawing with the padded coordinated
assembly of a ribbon-ready source. -/
structure CoordinatedAssemblyDrawingWitness
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (drawing : PeriodicGridDrawing) : Prop where
  width : source.erase.WidthAtMost 3
  occurrences :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 source.erase
  arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase
  variableOrdered :
    source.VariableRoutesInOccurrenceOrder presentation.routes
  clauseOrdered :
    source.TernaryClauseRoutesInClockwiseOrder presentation.routes
  drawing_eq :
    drawing = assembledDrawing
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered)

/-- The proof-backed polarity-normalized presentation retains an assembled
drawing.  This interface exposes its structural witnesses existentially so a
data-level compiler need not elaborate the concrete certificate terms. -/
theorem paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_witness
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps)
    (sourceDistinct : source.AllAtomsNodup)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    let routedPresentation :=
      haloBoundedRibbonReadyPresentation presentation sourceUnitSteps
    let routedSource := formula source sourcePlacement presentation.routes
    ∃ (routedWidth : routedSource.erase.WidthAtMost 3)
      (routedOccurrences :
        @PeriodicCNF.OccurrencesAtMost
          (PolarityNormalizedVariable Variable) instBEqOfDecidableEq
          (by infer_instance) 3 routedSource.erase)
      (routedArity :
        PeriodicOneInThreeNoUnits.ArityTwoOrThree routedSource.erase)
      (routedVariableOrdered :
        routedSource.VariableRoutesInOccurrenceOrder routedPresentation.routes)
      (routedClauseOrdered :
        routedSource.TernaryClauseRoutesInClockwiseOrder routedPresentation.routes),
      (paddedPeriodicThreeDMContinuousPlanarPresentation
        presentation sourceUnitSteps sourceDistinct occurrences arity
        variableOrdered clauseOrdered).drawing =
        assembledDrawing
          (paddedNormalizedCoordinatedRibbonThreeStrandRouting
            routedPresentation routedWidth routedOccurrences routedArity
            routedVariableOrdered routedClauseOrdered) := by
  dsimp only
  unfold paddedPeriodicThreeDMContinuousPlanarPresentation
  exact
    ⟨_, _, _, _, _,
      paddedNormalizedCoordinatedContinuousPlanarPresentation_drawing
        _ _ _ _ _ _ _⟩

/-- Structure-valued form of the drawing witness, suitable for concrete
reductions whose expanded variable types make dependent existential headers
expensive to elaborate. -/
theorem paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_certificate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps)
    (sourceDistinct : source.AllAtomsNodup)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    CoordinatedAssemblyDrawingWitness
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (haloBoundedRibbonReadyPresentation presentation sourceUnitSteps)
      (paddedPeriodicThreeDMContinuousPlanarPresentation
        presentation sourceUnitSteps sourceDistinct occurrences arity
        variableOrdered clauseOrdered).drawing := by
  rcases paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_witness
      presentation sourceUnitSteps sourceDistinct occurrences arity
      variableOrdered clauseOrdered with
    ⟨width, routedOccurrences, routedArity, routedVariableOrdered,
      routedClauseOrdered, drawingEq⟩
  exact
    ⟨width, routedOccurrences, routedArity, routedVariableOrdered,
      routedClauseOrdered, drawingEq⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

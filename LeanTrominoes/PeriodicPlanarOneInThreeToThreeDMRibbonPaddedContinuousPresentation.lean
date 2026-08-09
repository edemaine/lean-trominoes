import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFiniteGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedTranslatedPlanarity

/-!
# Continuous 3DM presentation of the final padded assembly

The translated-route separation proof supplies the last field of the global
assembly geometry interface.  Together with the previously established
normalized vertex distinctness and fundamental-square bounds, this packages
the final padded coordinated construction as a continuously planar periodic
3DM presentation, with no residual finite-check assumption.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PeriodicOneInThreePolarityNormalization

/-- Complete continuously planar geometry for the final padded normalized
coordinated assembly. -/
noncomputable def paddedNormalizedCoordinatedContinuousAssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (polarityNormalized : FormulaPolarityNormalized source.erase)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    ContinuousAssemblyGeometry routing := by
  dsimp only
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  refine
    { positionsNodup := ?_
      positionsInside := ?_
      continuouslyPlanar :=
        paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar
          presentation width polarityNormalized occurrences arity
          variableOrdered clauseOrdered }
  · change
      (assembledVertexPositions
        (paddedNormalizedRibbonThreeStrandRouting presentation)).Nodup
    exact
      paddedNormalizedRibbonAssembledVertexPositions_nodup presentation
  · change
      ∀ position ∈
          assembledVertexPositions
            (paddedNormalizedRibbonThreeStrandRouting presentation),
        (assembledDrawing
          (paddedNormalizedRibbonThreeStrandRouting presentation))
          |>.PositionInFundamentalSquare position
    exact
      paddedNormalizedRibbonAssembledVertexPositions_inside presentation

/-- The encoded periodic 3DM problem produced by the final padded normalized
coordinated assembly has a concrete continuously planar presentation. -/
noncomputable def paddedNormalizedCoordinatedContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (polarityNormalized : FormulaPolarityNormalized source.erase)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    let normalizedSource :=
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase
    (encodedProblem normalizedSource).ContinuousPlanarPresentation := by
  dsimp only
  exact
    (paddedNormalizedCoordinatedContinuousAssemblyGeometry
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered)
      |>.toContinuousPlanarPresentation

/-- Existence form of the final continuously planar presentation. -/
theorem paddedNormalizedCoordinatedHasContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (polarityNormalized : FormulaPolarityNormalized source.erase)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    let normalizedSource :=
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase
    (encodedProblem normalizedSource).HasContinuousPlanarPresentation := by
  dsimp only
  exact ⟨paddedNormalizedCoordinatedContinuousPlanarPresentation
    presentation width polarityNormalized occurrences arity
    variableOrdered clauseOrdered⟩

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

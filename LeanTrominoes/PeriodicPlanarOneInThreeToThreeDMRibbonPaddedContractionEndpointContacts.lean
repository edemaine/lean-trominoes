import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation
import LeanTrominoes.PeriodicThreeDMContractionEndpointContacts

/-!
# Endpoint contacts after contracting the padded 3DM assembly

The final padded coordinated assembly already supplies simple incidence
routes and complete separation of all their periodic lifts.  The generic
degree-two contraction theorem therefore applies directly to the concrete
3DM presentation used by the reduction.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PeriodicOneInThreePolarityNormalization

/-- The concrete padded normalized 3DM assembly retains endpoint-only route
contacts after every degree-two colored element is suppressed. -/
theorem paddedNormalizedCoordinatedContractedDrawing_routePointsMeetOnlyAtEndpoints
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
    let targetPresentation :=
      paddedNormalizedCoordinatedContinuousPlanarPresentation
        presentation width polarityNormalized occurrences arity
        variableOrdered clauseOrdered
    targetPresentation.toPlanarPresentation.contractedDrawing
      |>.RoutePointsMeetOnlyAtEndpoints := by
  dsimp only
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  let targetPresentation :=
    paddedNormalizedCoordinatedContinuousPlanarPresentation
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered
  have normalizedOccurrences :
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase.OccurrencesAtMost 3 := by
    simpa [normalizedSource] using
      normalizedSource_occurrencesAtMost
        (source.scale 2) (placement.scale 2) (by simpa using occurrences)
  have normalizedArity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase := by
    simpa [normalizedSource] using
      normalizedSource_arityTwoOrThree
        (source.scale 2) (placement.scale 2) (by simpa using arity)
  have degree :
      (encodedProblem
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase).DegreeTwoOrThree :=
    encodedProblem_degreeTwoOrThree _
      (problem_degreeTwoOrThree _ normalizedOccurrences normalizedArity)
  apply
    targetPresentation.toPlanarPresentation
      |>.contractedDrawing_routePointsMeetOnlyAtEndpoints degree
  · change (assembledDrawing routing).LiftedRoutesAvoidEachOther
    exact
      paddedNormalizedCoordinatedLiftedRoutes_avoidEachOther
        presentation width polarityNormalized occurrences arity
        variableOrdered clauseOrdered
  · change
      ∀ route ∈ (assembledDrawing routing).edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route
    simpa [routing, assembledDrawing] using
      paddedNormalizedCoordinatedAssembledEdgeRoutes_simple
        presentation width occurrences arity
        variableOrdered clauseOrdered

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

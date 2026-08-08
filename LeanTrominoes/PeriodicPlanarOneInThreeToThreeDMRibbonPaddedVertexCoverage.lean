import LeanTrominoes.PeriodicThreeDMIncidenceVertexCoverage
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFiniteGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting

/-!
# Vertex endpoint coverage in the padded ribbon assembly

The natural-number 3DM encoding has degree two or three at every colored
element, so its incidence graph has no isolated vertices.  Exact assembled
route endpoints and the already proved normalized vertex bounds therefore
cover every stored graph-vertex position by a lifted route-segment endpoint.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Any assembled drawing with the established vertex-position obligations
covers its vertices by route-segment endpoints as soon as the encoded target
has degree two or three. -/
theorem assembledDrawing_vertexPositionsCoveredBySegmentEndpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (degree : (encodedProblem source).DegreeTwoOrThree)
    (positionsNodup :
      (assembledVertexPositions routing).Nodup)
    (positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position) :
    (assembledDrawing routing).VertexPositionsCoveredBySegmentEndpoints := by
  let compatible :=
    assembledDrawing_isCompatible_of_positions
      routing positionsNodup positionsInside
  exact
    PeriodicThreeDM.incidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
      (encodedProblem source) (assembledDrawing routing)
      compatible degree

/-- Every graph vertex in the final padded normalized coordinated assembly
is an endpoint of some lifted route segment. -/
theorem paddedNormalizedCoordinatedAssembledVertexPositions_covered
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered
    (assembledDrawing routing).VertexPositionsCoveredBySegmentEndpoints := by
  dsimp only
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity
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
  have positionsNodup :
      (assembledVertexPositions routing).Nodup := by
    change
      (assembledVertexPositions
        (paddedNormalizedRibbonThreeStrandRouting presentation)).Nodup
    exact
      paddedNormalizedRibbonAssembledVertexPositions_nodup presentation
  have positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position := by
    change
      ∀ position ∈
          assembledVertexPositions
            (paddedNormalizedRibbonThreeStrandRouting presentation),
        (assembledDrawing
          (paddedNormalizedRibbonThreeStrandRouting presentation))
          |>.PositionInFundamentalSquare position
    exact
      paddedNormalizedRibbonAssembledVertexPositions_inside presentation
  exact
    assembledDrawing_vertexPositionsCoveredBySegmentEndpoints
      routing degree positionsNodup positionsInside

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

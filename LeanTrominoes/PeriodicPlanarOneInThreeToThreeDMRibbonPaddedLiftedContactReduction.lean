import LeanTrominoes.PeriodicGridDrawingExpandedLiftedInteriorContactSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedAssembledRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedVertexCoverage

/-!
# Reducing padded lifted contacts to nonzero period shifts

The final padded assembly already separates every pair of distinct stored
routes in one fundamental period.  Incidence-tag uniqueness transports that
statement to numeric route indices.  Consequently the only route-contact
geometry still needed for continuous periodic planarity is separation from
nonzero relative lattice translates.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Distinct numeric routes stored by the final padded normalized assembly
avoid all three forms of segment-interior contact. -/
theorem paddedNormalizedCoordinatedAssembledStoredRoutes_avoidInteriors
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
    (assembledDrawing routing).StoredRoutesAvoidInteriorContacts := by
  dsimp only
  let normalizedSource :=
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase
  let problem := encodedProblem normalizedSource
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity
      variableOrdered clauseOrdered
  intro first firstMember second secondMember indicesDifferent
  have firstMappedMember :
      first ∈
        (problem.incidenceTags.map
          (assembledRouteAtTag routing)).zipIdx := by
    simpa [assembledDrawing, assembledEdgeRoutes,
      problem, normalizedSource, routing] using firstMember
  have secondMappedMember :
      second ∈
        (problem.incidenceTags.map
          (assembledRouteAtTag routing)).zipIdx := by
    simpa [assembledDrawing, assembledEdgeRoutes,
      problem, normalizedSource, routing] using secondMember
  have firstIndexLt : first.2 < problem.incidenceTags.length := by
    simpa using List.snd_lt_of_mem_zipIdx firstMappedMember
  have secondIndexLt : second.2 < problem.incidenceTags.length := by
    simpa using List.snd_lt_of_mem_zipIdx secondMappedMember
  let firstTag := problem.incidenceTags[first.2]'firstIndexLt
  let secondTag := problem.incidenceTags[second.2]'secondIndexLt
  have firstTagMember : firstTag ∈ problem.incidenceTags :=
    List.getElem_mem firstIndexLt
  have secondTagMember : secondTag ∈ problem.incidenceTags :=
    List.getElem_mem secondIndexLt
  have firstRouteEq :
      first.1 = assembledRouteAtTag routing firstTag := by
    simpa [firstTag] using
      (List.mem_zipIdx' firstMappedMember).2
  have secondRouteEq :
      second.1 = assembledRouteAtTag routing secondTag := by
    simpa [secondTag] using
      (List.mem_zipIdx' secondMappedMember).2
  have tagsDifferent : firstTag ≠ secondTag := by
    intro tagsEqual
    apply indicesDifferent
    exact
      (PeriodicThreeDM.incidenceTags_nodup problem).getElem_inj_iff.mp
        tagsEqual
  rw [firstRouteEq, secondRouteEq]
  exact
    paddedNormalizedCoordinatedAssembledRouteAtTags_avoidInteriors
      presentation width occurrences arity variableOrdered clauseOrdered
      firstTag secondTag firstTagMember secondTagMember tagsDifferent

/-- The 24 nonzero halo-neighbor shifts suffice for all nonzero translated
route pairs in the final padded coordinated assembly. -/
theorem paddedNormalizedCoordinatedNonzeroRelativeLiftedRoutes_avoidInteriors_of_doubleNeighbor
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (finite :
      let routing :=
        paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered
      (assembledDrawing routing)
        |>.DoubleNeighborNonzeroRelativeLiftedRoutesAvoidInteriorContacts) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered
    (assembledDrawing routing)
      |>.NonzeroRelativeLiftedRoutesAvoidInteriorContacts := by
  dsimp only at finite ⊢
  apply
    PeriodicGridDrawing.nonzeroRelativeLiftedRoutesAvoidInteriorContacts_of_doubleNeighbor
  · exact
      paddedNormalizedCoordinatedAssembledRoutePointsInExpandedSquare
        presentation width occurrences arity variableOrdered clauseOrdered
  · exact finite

/-- Once nonzero relative translates are separated, the final padded
assembly satisfies the complete relative lifted contact predicate. -/
theorem paddedNormalizedCoordinatedRelativeLiftedRoutes_avoidInteriors_of_nonzero
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (nonzero :
      let routing :=
        paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered
      (assembledDrawing routing)
        |>.NonzeroRelativeLiftedRoutesAvoidInteriorContacts) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered
    (assembledDrawing routing).RelativeLiftedRoutesAvoidInteriorContacts := by
  dsimp only at nonzero ⊢
  apply
    PeriodicGridDrawing.relativeLiftedRoutesAvoidInteriorContacts_of_stored_of_nonzero
  · exact
      paddedNormalizedCoordinatedAssembledStoredRoutes_avoidInteriors
        presentation width occurrences arity variableOrdered clauseOrdered
  · exact nonzero

/-- Nonzero translated-route separation is the sole remaining geometric
input needed to make the final padded assembly continuously planar. -/
theorem paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar_of_nonzero
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (nonzero :
      let routing :=
        paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered
      (assembledDrawing routing)
        |>.NonzeroRelativeLiftedRoutesAvoidInteriorContacts) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered
    (assembledDrawing routing).IsContinuouslyPlanar := by
  dsimp only at nonzero ⊢
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity
      variableOrdered clauseOrdered
  apply
    PeriodicGridDrawing.isContinuouslyPlanar_of_relativeLiftedRoutesAvoidInteriorContacts
  · exact
      paddedNormalizedCoordinatedRelativeLiftedRoutes_avoidInteriors_of_nonzero
        presentation width occurrences arity variableOrdered clauseOrdered
        nonzero
  · simpa [assembledDrawing] using
      paddedNormalizedCoordinatedAssembledEdgeRoutes_simple
        presentation width occurrences arity variableOrdered clauseOrdered
  · exact
      paddedNormalizedCoordinatedAssembledVertexPositions_covered
        presentation width occurrences arity variableOrdered clauseOrdered
  · exact assembledDrawing_isOrthogonal routing

/-- Checking the 24 nonzero halo-neighbor shifts is enough to prove exact
continuous planarity of the final padded coordinated assembly. -/
theorem paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar_of_doubleNeighbor
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (finite :
      let routing :=
        paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered
      (assembledDrawing routing)
        |>.DoubleNeighborNonzeroRelativeLiftedRoutesAvoidInteriorContacts) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered
    (assembledDrawing routing).IsContinuouslyPlanar := by
  dsimp only at finite ⊢
  apply
    paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar_of_nonzero
      presentation width occurrences arity variableOrdered clauseOrdered
  exact
    paddedNormalizedCoordinatedNonzeroRelativeLiftedRoutes_avoidInteriors_of_doubleNeighbor
      presentation width occurrences arity variableOrdered clauseOrdered finite

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

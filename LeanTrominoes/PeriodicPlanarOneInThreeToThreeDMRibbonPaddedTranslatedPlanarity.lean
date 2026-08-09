import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedLiftedContactReduction

/-!
# Continuous planarity of the final padded assembly

The general translated assembled-route theorem specializes to the doubled,
anchor-normalized source.  Numeric incidence-tag lookup transports it to all
stored routes.  Together with same-period separation, this gives complete
endpoint-aware separation of all lifted route occurrences, as well as the
continuous planarity certificate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOneInThreePolarityNormalization

/-- Complete typed routes in the final padded normalized assembly avoid every
nonzero relative period translate. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_avoids_nonzeroTranslateInteriors
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
    (first second :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (firstColor secondColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceRoute routing first firstColor)
      (translatePolyline (routing.periodTranslation translate)
        (assembledTypedIncidenceRoute routing second secondColor)) := by
  dsimp only
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  have anchorsZero : HasZeroClauseAnchors
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)) :=
    normalizedPositionedSource_hasZeroClauseAnchors
      (source.scale 2) (placement.scale 2)
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
  have separated :=
    coordinatedSourceAssembledTypedIncidenceRoute_avoids_nonzeroTranslateInteriors
      normalized anchorsZero normalizedOccurrences normalizedArity
      (paddedNormalizedSource_widthAtMostThree width) compatible
      (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
      first second firstColor secondColor translate translateNonzero
  simpa [paddedNormalizedCoordinatedRibbonThreeStrandRouting,
    normalized, compatible, coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting,
    ThreeStrandRouting.periodTranslation, ribbonMacrocellOrigin,
    standardThreeStrandLayout, PeriodicVariablePlacement.translation,
    Cell.scale, mul_assoc] using separated

/-- Complete typed routes in the final padded normalized assembly have
endpoint-aware separation from every nonzero relative period translate. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_avoids_nonzeroTranslate
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
    (first second :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (firstColor secondColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidEachOther
      (assembledTypedIncidenceRoute routing first firstColor)
      (translatePolyline (routing.periodTranslation translate)
        (assembledTypedIncidenceRoute routing second secondColor)) := by
  dsimp only
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  have anchorsZero : HasZeroClauseAnchors
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)) :=
    normalizedPositionedSource_hasZeroClauseAnchors
      (source.scale 2) (placement.scale 2)
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
  have separated :=
    coordinatedSourceAssembledTypedIncidenceRoute_avoids_nonzeroTranslate
      normalized anchorsZero normalizedOccurrences normalizedArity
      (paddedNormalizedSource_widthAtMostThree width) compatible
      (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
      first second firstColor secondColor translate translateNonzero
  simpa [paddedNormalizedCoordinatedRibbonThreeStrandRouting,
    normalized, compatible, coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting,
    ThreeStrandRouting.periodTranslation, ribbonMacrocellOrigin,
    standardThreeStrandLayout, PeriodicVariablePlacement.translation,
    Cell.scale, mul_assoc] using separated

/-- Genuine numeric incidence tags select translated routes satisfying the
same nonzero-shift separation theorem. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTags_avoid_nonzeroTranslateInteriors
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
    (first second : PeriodicThreeDM.IncidenceTag)
    (firstMember : first ∈
      (encodedProblem
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase).incidenceTags)
    (secondMember : second ∈
      (encodedProblem
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase).incidenceTags)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidInteriorContacts
      (assembledRouteAtTag routing first)
      (translatePolyline (routing.periodTranslation translate)
        (assembledRouteAtTag routing second)) := by
  dsimp only
  let normalizedSource :=
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  have firstIndexLt : first.tripleIndex <
      (triples normalizedSource).length := by
    simpa [encodedProblem, TypedProblem.encode, problem,
      normalizedSource] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem normalizedSource) firstMember
  have secondIndexLt : second.tripleIndex <
      (triples normalizedSource).length := by
    simpa [encodedProblem, TypedProblem.encode, problem,
      normalizedSource] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem normalizedSource) secondMember
  let firstTriple :
      {triple : Triple Variable // triple ∈ triples normalizedSource} :=
    ⟨(triples normalizedSource)[first.tripleIndex]'firstIndexLt,
      List.getElem_mem firstIndexLt⟩
  let secondTriple :
      {triple : Triple Variable // triple ∈ triples normalizedSource} :=
    ⟨(triples normalizedSource)[second.tripleIndex]'secondIndexLt,
      List.getElem_mem secondIndexLt⟩
  have separated :=
    paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_avoids_nonzeroTranslateInteriors
      presentation width occurrences arity variableOrdered clauseOrdered
      firstTriple secondTriple first.color second.color translate
      translateNonzero
  simpa [assembledRouteAtTag, firstIndexLt, secondIndexLt,
    firstTriple, secondTriple, routing, normalizedSource] using separated

/-- Genuine numeric incidence tags select nonzero-translated routes with
full endpoint-aware separation. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTags_avoid_nonzeroTranslate
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
    (first second : PeriodicThreeDM.IncidenceTag)
    (firstMember : first ∈
      (encodedProblem
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase).incidenceTags)
    (secondMember : second ∈
      (encodedProblem
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase).incidenceTags)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidEachOther
      (assembledRouteAtTag routing first)
      (translatePolyline (routing.periodTranslation translate)
        (assembledRouteAtTag routing second)) := by
  dsimp only
  let normalizedSource :=
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  have firstIndexLt : first.tripleIndex <
      (triples normalizedSource).length := by
    simpa [encodedProblem, TypedProblem.encode, problem,
      normalizedSource] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem normalizedSource) firstMember
  have secondIndexLt : second.tripleIndex <
      (triples normalizedSource).length := by
    simpa [encodedProblem, TypedProblem.encode, problem,
      normalizedSource] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem normalizedSource) secondMember
  let firstTriple :
      {triple : Triple Variable // triple ∈ triples normalizedSource} :=
    ⟨(triples normalizedSource)[first.tripleIndex]'firstIndexLt,
      List.getElem_mem firstIndexLt⟩
  let secondTriple :
      {triple : Triple Variable // triple ∈ triples normalizedSource} :=
    ⟨(triples normalizedSource)[second.tripleIndex]'secondIndexLt,
      List.getElem_mem secondIndexLt⟩
  have separated :=
    paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_avoids_nonzeroTranslate
      presentation width occurrences arity variableOrdered clauseOrdered
      firstTriple secondTriple first.color second.color translate
      translateNonzero
  simpa [assembledRouteAtTag, firstIndexLt, secondIndexLt,
    firstTriple, secondTriple, routing, normalizedSource] using separated

/-- All stored routes in the final padded normalized drawing avoid every
nonzero relative lifted translate. -/
theorem paddedNormalizedCoordinatedNonzeroRelativeLiftedRoutes_avoidInteriors
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
        presentation width occurrences arity variableOrdered clauseOrdered
    (assembledDrawing routing)
      |>.NonzeroRelativeLiftedRoutesAvoidInteriorContacts := by
  dsimp only
  let normalizedSource :=
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase
  let problem := encodedProblem normalizedSource
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  intro first firstMember second secondMember translate translateNonzero
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
    simpa [firstTag] using (List.mem_zipIdx' firstMappedMember).2
  have secondRouteEq :
      second.1 = assembledRouteAtTag routing secondTag := by
    simpa [secondTag] using (List.mem_zipIdx' secondMappedMember).2
  rw [firstRouteEq, secondRouteEq]
  simpa [translatePolyline, assembledDrawing_periodTranslation] using
    paddedNormalizedCoordinatedAssembledRouteAtTags_avoid_nonzeroTranslateInteriors
      presentation width occurrences arity variableOrdered clauseOrdered
      firstTag secondTag firstTagMember secondTagMember translate
      translateNonzero

/-- All distinct lifted occurrences of routes in the final padded normalized
drawing have endpoint-aware separation, including both same-period pairs and
all nonzero relative translates. -/
theorem paddedNormalizedCoordinatedRelativeLiftedRoutes_avoidEachOther
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
    (assembledDrawing routing).RelativeLiftedRoutesAvoidEachOther := by
  dsimp only
  let normalizedSource :=
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase
  let problem := encodedProblem normalizedSource
  let routing :=
    paddedNormalizedCoordinatedRibbonThreeStrandRouting
      presentation width occurrences arity variableOrdered clauseOrdered
  intro first firstMember second secondMember translate occurrencesDifferent
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
    simpa [firstTag] using (List.mem_zipIdx' firstMappedMember).2
  have secondRouteEq :
      second.1 = assembledRouteAtTag routing secondTag := by
    simpa [secondTag] using (List.mem_zipIdx' secondMappedMember).2
  rw [firstRouteEq, secondRouteEq]
  by_cases translateZero : translate = (0, 0)
  · subst translate
    have indicesDifferent : first.2 ≠ second.2 := by
      intro indicesEqual
      apply occurrencesDifferent
      simp [indicesEqual]
    have tagsDifferent : firstTag ≠ secondTag := by
      intro tagsEqual
      apply indicesDifferent
      exact
        (PeriodicThreeDM.incidenceTags_nodup problem).getElem_inj_iff.mp
          tagsEqual
    rw [PeriodicGridDrawing.map_add_periodTranslation_zero]
    simpa [routing] using
      paddedNormalizedCoordinatedAssembledRouteAtTags_avoidEachOther
        presentation width polarityNormalized occurrences arity
        variableOrdered clauseOrdered
        firstTag secondTag firstTagMember secondTagMember tagsDifferent
  · simpa [translatePolyline, assembledDrawing_periodTranslation] using
      paddedNormalizedCoordinatedAssembledRouteAtTags_avoid_nonzeroTranslate
        presentation width occurrences arity variableOrdered clauseOrdered
        firstTag secondTag firstTagMember secondTagMember translate
        translateZero

/-- The equivalent absolute-shift formulation of complete lifted route
separation for the final padded normalized drawing. -/
theorem paddedNormalizedCoordinatedLiftedRoutes_avoidEachOther
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
    (assembledDrawing routing).LiftedRoutesAvoidEachOther := by
  dsimp only
  apply
    (PeriodicGridDrawing.liftedRoutesAvoidEachOther_iff_relative _).mpr
  exact
    paddedNormalizedCoordinatedRelativeLiftedRoutes_avoidEachOther
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered

/-- Consequently, listed points of distinct lifted route occurrences can
coincide only when both are endpoints of their respective routes. -/
theorem paddedNormalizedCoordinatedAssembledDrawing_routePointsMeetOnlyAtEndpoints
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
    (assembledDrawing routing).RoutePointsMeetOnlyAtEndpoints := by
  dsimp only
  apply
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
  · exact
      paddedNormalizedCoordinatedLiftedRoutes_avoidEachOther
        presentation width polarityNormalized occurrences arity
        variableOrdered clauseOrdered
  · simpa [assembledDrawing] using
      paddedNormalizedCoordinatedAssembledEdgeRoutes_simple
        presentation width occurrences arity variableOrdered clauseOrdered

/-- The final padded normalized coordinated assembly is continuously planar,
with no remaining finite-neighbor separation hypothesis. -/
theorem paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar
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
    (assembledDrawing routing).IsContinuouslyPlanar := by
  dsimp only
  apply
    paddedNormalizedCoordinatedAssembledDrawing_isContinuouslyPlanar_of_nonzero
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered
  exact
    paddedNormalizedCoordinatedNonzeroRelativeLiftedRoutes_avoidInteriors
      presentation width occurrences arity variableOrdered clauseOrdered

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

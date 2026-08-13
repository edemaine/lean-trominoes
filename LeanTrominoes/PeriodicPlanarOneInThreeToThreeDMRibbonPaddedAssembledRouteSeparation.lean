/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedCoordinatedRouting

/-!
# Stored-route separation in the final padded assembly

The general source-assembly theorem specializes to the doubled,
anchor-normalized source once the source formula has the polarity convention
used by the three endpoint-clear variable tables.  This file records the
resulting separation first for typed incidences and then for the genuine
numeric incidence tags used by the assembled periodic drawing.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOneInThreePolarityNormalization

/-- Distinct colored typed incidences in the final padded normalized
assembly have full endpoint-aware separation. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoutes_avoidEachOther
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (first second :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (firstColor secondColor : WireColor)
    (different : (first.1, firstColor) ≠ (second.1, secondColor)) :
    RoutesAvoidEachOther
      (assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        first firstColor)
      (assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        second secondColor) := by
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
  have normalizedPolarity :
      FormulaPolarityNormalized
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase := by
    rw [normalizedPositionedSource,
      PositionedPeriodicCNF.erase_anchorNormalize,
      PositionedPeriodicCNF.erase_scale]
    exact FormulaPolarityNormalized.anchorNormalize polarityNormalized
  simpa [paddedNormalizedCoordinatedRibbonThreeStrandRouting,
    normalized, compatible] using
    coordinatedSourceAssembledTypedIncidenceRoutes_avoidEachOther
      normalized anchorsZero normalizedOccurrences normalizedArity
      (paddedNormalizedSource_widthAtMostThree width) normalizedPolarity
      compatible
      (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
      first second firstColor secondColor different

/-- Distinct colored typed incidences in the final padded normalized assembly
avoid every kind of segment-interior contact. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoutes_avoidInteriors
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
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    (first second :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (firstColor secondColor : WireColor)
    (different : (first.1, firstColor) ≠ (second.1, secondColor)) :
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        first firstColor)
      (assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        second secondColor) := by
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
  have normalizedPolarity :
      FormulaPolarityNormalized
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase := by
    rw [normalizedPositionedSource,
      PositionedPeriodicCNF.erase_anchorNormalize,
      PositionedPeriodicCNF.erase_scale]
    exact FormulaPolarityNormalized.anchorNormalize polarityNormalized
  simpa [paddedNormalizedCoordinatedRibbonThreeStrandRouting,
    normalized, compatible] using
    coordinatedSourceAssembledTypedIncidenceRoutes_avoidInteriors
      normalized anchorsZero normalizedOccurrences normalizedArity
      (paddedNormalizedSource_widthAtMostThree width) normalizedPolarity
      compatible
      (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
      first second firstColor secondColor different

/-- Distinct genuine incidence tags select continuously separated routes in
the final padded normalized assembled drawing. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTags_avoidInteriors
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
    (different : first ≠ second) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidInteriorContacts
      (assembledRouteAtTag routing first)
      (assembledRouteAtTag routing second) := by
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
  have keysDifferent :
      (firstTriple.1, first.color) ≠
        (secondTriple.1, second.color) := by
    intro keysEq
    apply different
    rcases Prod.mk.inj keysEq with ⟨tripleEq, colorEq⟩
    have indexEq : first.tripleIndex = second.tripleIndex :=
      (triples_nodup normalizedSource).getElem_inj_iff.mp tripleEq
    cases first
    cases second
    simp_all
  have separated :=
    paddedNormalizedCoordinatedAssembledTypedIncidenceRoutes_avoidInteriors
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered
      firstTriple secondTriple first.color second.color keysDifferent
  simpa [assembledRouteAtTag, firstIndexLt, secondIndexLt,
    firstTriple, secondTriple, routing, normalizedSource] using separated

/-- Distinct genuine incidence tags select endpoint-aware separated routes
in the final padded normalized assembled drawing. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTags_avoidEachOther
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
    (different : first ≠ second) :
    let routing :=
      paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity variableOrdered clauseOrdered
    RoutesAvoidEachOther
      (assembledRouteAtTag routing first)
      (assembledRouteAtTag routing second) := by
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
  have keysDifferent :
      (firstTriple.1, first.color) ≠
        (secondTriple.1, second.color) := by
    intro keysEq
    apply different
    rcases Prod.mk.inj keysEq with ⟨tripleEq, colorEq⟩
    have indexEq : first.tripleIndex = second.tripleIndex :=
      (triples_nodup normalizedSource).getElem_inj_iff.mp tripleEq
    cases first
    cases second
    simp_all
  have separated :=
    paddedNormalizedCoordinatedAssembledTypedIncidenceRoutes_avoidEachOther
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered
      firstTriple secondTriple first.color second.color keysDifferent
  simpa [assembledRouteAtTag, firstIndexLt, secondIndexLt,
    firstTriple, secondTriple, routing, normalizedSource] using separated

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

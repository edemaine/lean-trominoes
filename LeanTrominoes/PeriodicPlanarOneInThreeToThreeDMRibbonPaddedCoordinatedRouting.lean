/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouteLength
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouting
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSimplicity

/-!
# Padded normalized coordinated ribbon routing

This is the final occurrence-routing object: double the ribbon-ready source,
normalize its clause anchors, install the coordinated endpoint fans, and join
them to the three colored corridor cores.  The padding length theorem and the
transported clockwise-order certificate make separation unconditional from
the source promises.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Width three survives source doubling and anchor normalization. -/
theorem paddedNormalizedSource_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (width : source.erase.WidthAtMost 3) :
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase.WidthAtMost 3 := by
  simpa [normalizedPositionedSource] using
    PeriodicCNF.anchorNormalize_widthAtMost
      (source.scale 2).erase 3 (by simpa using width)

/-- The final coordinated routing on the doubled, normalized source. -/
noncomputable def paddedNormalizedCoordinatedRibbonThreeStrandRouting
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
    ThreeStrandRouting
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase :=
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  coordinatedSourceRibbonThreeStrandRouting
    normalized
    (paddedNormalizedSource_widthAtMostThree width)
    (paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered)

/-- Every listed point of a final coordinated occurrence route remains in
the assembled open one-cell halo. -/
theorem paddedNormalizedCoordinatedRibbonRoute_pointsInsideExpandedSquare
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
    (entry :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase)
    (color : WireColor) {point : Cell}
    (pointMember :
      point ∈
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered).route entry color) :
    (assembledDrawing
      (paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered))
      |>.PositionInExpandedSquare point := by
  let padded := presentation.scaleTwo
  let normalized :=
    normalizedRibbonReadyIncidencePresentation padded
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  let fans :=
    coordinatedSourceRibbonEndpointFanSystem
      normalized.toPlanarIncidencePresentation
      (paddedNormalizedSource_widthAtMostThree width) compatible
  change point ∈ fans.occurrenceThreeStrandRoute entry color
    at pointMember
  change
    (assembledDrawing
      (ribbonThreeStrandRouting
        normalized.toContinuousPlanarIncidencePresentation))
      |>.PositionInExpandedSquare point
  rcases
      fans.occurrenceThreeStrandRoute_points_bounded
        entry color pointMember with
    variableBounded | corridorBounded | clauseBounded
  · apply inRibbonMacrocell_insideExpandedSquare
      normalized.toContinuousPlanarIncidencePresentation
    · exact
        occurrenceUnitSourceRoute_pointsInsideExpandedSquareWithUpperMargin
          normalized.toPlanarIncidencePresentation
          (padded.toPlanarIncidencePresentation
            |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
              presentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin)
          entry
          (occurrenceUnitSourceRoute_variableEndpoint_mem
            normalized.toPlanarIncidencePresentation entry)
    · exact variableBounded
  · rcases corridorBounded with
      ⟨center, centerMember, bounded⟩
    apply inRibbonMacrocell_insideExpandedSquare
      normalized.toContinuousPlanarIncidencePresentation
    · exact
        occurrenceUnitSourceRoute_pointsInsideExpandedSquareWithUpperMargin
          normalized.toPlanarIncidencePresentation
          (padded.toPlanarIncidencePresentation
            |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
              presentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin)
          entry centerMember
    · exact bounded
  · let data :=
      occurrenceSpliceData normalized.toPlanarIncidencePresentation entry
    apply inRibbonMacrocell_insideExpandedSquare
      normalized.toContinuousPlanarIncidencePresentation
    · exact
        occurrenceUnitSourceRoute_pointsInsideExpandedSquareWithUpperMargin
          normalized.toPlanarIncidencePresentation
          (padded.toPlanarIncidencePresentation
            |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
              presentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin)
          entry
          (occurrenceUnitSourceRoute_clauseEndpoint_mem
            normalized.toPlanarIncidencePresentation entry)
    · exact clauseBounded

/-- Every occurrence-route suffix in the final padded normalized routing is
geometrically simple. -/
theorem paddedNormalizedCoordinatedRibbonThreeStrandRouting_route_simple
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
    (entry :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      ((paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered).route entry color) := by
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  exact
    coordinatedSourceRibbonThreeStrandRouting_route_simple_of_length_ge_three
      normalized
      (paddedNormalizedSource_widthAtMostThree width)
      compatible entry color
      (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three
        presentation entry)

/-- Every assembled typed incidence route in the final padded normalized
coordinated routing is geometrically simple. -/
theorem paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_simple
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
    (triple :
      {triple : Triple Variable //
        triple ∈ triples
          (normalizedPositionedSource
            (source.scale 2) (placement.scale 2)).erase})
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledTypedIncidenceRoute
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        triple color) := by
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  exact coordinatedSourceAssembledTypedIncidenceRoute_simple
    normalized
    (paddedNormalizedSource_widthAtMostThree width)
    compatible
    (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
    triple color

/-- Total incidence-tag lookup preserves route simplicity, including its
unreachable empty fallback branch. -/
theorem paddedNormalizedCoordinatedAssembledRouteAtTag_simple
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
    (tag : PeriodicThreeDM.IncidenceTag) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledRouteAtTag
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered)
        tag) := by
  unfold assembledRouteAtTag
  split
  next indexLt =>
    exact
      paddedNormalizedCoordinatedAssembledTypedIncidenceRoute_simple
        presentation width occurrences arity
        variableOrdered clauseOrdered
        ⟨_, List.getElem_mem indexLt⟩ tag.color
  next indexNotLt =>
    simp [LocalIncidenceDrawing.RouteIsSimple, gridPolylineSegments]

/-- Every route stored in the final padded normalized coordinated assembly
is geometrically simple. -/
theorem paddedNormalizedCoordinatedAssembledEdgeRoutes_simple
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
    ∀ route ∈ assembledEdgeRoutes
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity
          variableOrdered clauseOrdered),
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  unfold assembledEdgeRoutes at routeMember
  rcases List.mem_map.mp routeMember with ⟨tag, tagMember, rfl⟩
  exact paddedNormalizedCoordinatedAssembledRouteAtTag_simple
    presentation width occurrences arity
    variableOrdered clauseOrdered tag

set_option maxHeartbeats 1000000 in
/-- Every pair of distinct colored occurrence routes in the final
coordinated routing is contact-free. -/
theorem paddedNormalizedCoordinatedRibbonThreeStrandRoutes_strictlyAvoidEachOther
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
    {first second :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      ((paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered).route first firstColor)
      ((paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered).route second secondColor) := by
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  apply coordinatedSourceRibbonThreeStrandRoutes_strictlyAvoidEachOther
    normalized
    (paddedNormalizedSource_widthAtMostThree width)
    compatible
    (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
    different

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

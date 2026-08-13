/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreClauseFanSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreCorridorSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-!
# Source variable-site cores versus clause stubs

The one-cell inset certificate separates a routed variable-site prefix from
the clause fan at every adjacent lifted clause target; ordinary macrocell
bounds handle far targets.  This closes the same-incidence splice by proving
that the assembled prefix avoids the complete coordinated occurrence route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A constructed routed variable-site prefix strictly avoids the
coordinated clause stub of the same occurrence. -/
theorem constructedRoutedVariablePrefix_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesStrictlyAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position entry.1.1
  let secondCenter := occurrenceSourceClauseTarget planar entry
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · exact False.elim
      (occurrenceSourceVariablePosition_ne_clauseTarget
        presentation entry entry centersEqual)
  · exact routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        constructedRoutedVariablePrefix_points_bounded
          planar entry color member)
      (fun point member =>
        occurrenceCoordinatedRibbonClauseStub_points_bounded
          planar compatible entry color member)
      centersFar
  · let variableData := sourceVariableRibbonFanData planar entry
    let clauseIndex :=
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2
    let clauseData := sourceClauseRibbonFanData planar clauseIndex
    let slot := occurrenceVariableSiteSlot entry.1.2
    let group := occurrenceClauseTerminalGroup source.erase entry
    let lane := routedRibbonLane source.erase entry color
    let offset := Cell.sub secondCenter firstCenter
    have variableActive : variableData.SlotActive slot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
        planar entry
    have clauseMember :
        entry ∈ activeClauseOccurrenceEntries
          source.erase clauseIndex :=
      entry.mem_activeClauseOccurrenceEntries
    have clauseActive : clauseData.GroupActive group :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar clauseIndex entry clauseMember
    have localAvoid :=
      variableData.routedVariableSiteRoute_strictlyAvoids_adjacentClauseCoordinatedRoute
        slot variableActive color clauseData
        (compatible.2 entry) group clauseActive lane
        offset centersAdjacent
    rw [sourceVariableRibbonFanData_routedVariableSiteRoute
      planar entry color] at localAvoid
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have originEq :
        Cell.add
            (Cell.scale standardThreeStrandLayout.factor offset)
            (ribbonMacrocellOrigin firstCenter) =
          ribbonMacrocellOrigin secondCenter := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases secondCenter with ⟨secondX, secondY⟩
      apply Prod.ext <;>
        simp [offset, ribbonMacrocellOrigin,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring
    have clauseTranslation :
        translatePolyline (ribbonMacrocellOrigin firstCenter)
            (translatePolyline
              (Cell.scale standardThreeStrandLayout.factor offset)
              (clauseData.coordinatedRoute group lane)) =
          translatePolyline (ribbonMacrocellOrigin secondCenter)
            (clauseData.coordinatedRoute group lane) := by
      rw [translatePolyline_add, originEq]
    rw [translatedRoutedVariableSiteRoute_eq_constructedPrefix
      entry color, clauseTranslation] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonClauseStub,
      planar, variableData, clauseData, slot, clauseIndex,
      group, lane, firstCenter, secondCenter] using translatedAvoid

/-- The constructed variable prefix avoids the complete coordinated route
of its occurrence: variable stub, corridor core, and clause stub. -/
theorem constructedRoutedVariablePrefix_avoids_occurrenceThreeStrandRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry color) := by
  unfold RibbonEndpointFanSystem.occurrenceThreeStrandRoute
  apply RoutesAvoidEachOther.join_right_of_strict_suffix
    (constructedRoutedVariablePrefix_avoids_variableStub_join_corridorCore
      presentation compatible entry color)
    (constructedRoutedVariablePrefix_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
      presentation compatible entry color)
  · apply joinAtEndpoint_getLast?
    · exact
        (occurrenceCoordinatedRibbonVariableStub_endpoints
          presentation.toPlanarIncidencePresentation compatible
          entry color).2
    · exact
        (occurrenceRibbonCorridorCore_endpoints
          presentation.toPlanarIncidencePresentation entry color).1
    · exact
        (occurrenceRibbonCorridorCore_endpoints
          presentation.toPlanarIncidencePresentation entry color).2
  · exact
      (occurrenceCoordinatedRibbonClauseStub_endpoints
        presentation.toPlanarIncidencePresentation width compatible
        entry color).1

/-- In the actual coordinated global routing, the assembled common variable
prefix avoids the complete occurrence-route suffix to which it is joined. -/
theorem assembledRoutedVariablePrefix_avoids_coordinatedSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let routing :=
      coordinatedSourceRibbonThreeStrandRouting
        presentation width compatible
    RoutesAvoidEachOther
      (assembledRoutedVariablePrefix routing entry color)
      (routing.route entry color) := by
  dsimp only
  rw [assembledRoutedVariablePrefix_eq_constructed
    (coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible) rfl entry color]
  rw [coordinatedSourceRibbonThreeStrandRouting_route]
  exact constructedRoutedVariablePrefix_avoids_occurrenceThreeStrandRoute
    presentation width compatible entry color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

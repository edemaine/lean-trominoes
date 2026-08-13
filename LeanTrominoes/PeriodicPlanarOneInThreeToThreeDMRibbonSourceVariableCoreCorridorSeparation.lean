/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreMacrocellSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAssembledVariablePrefix
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation

/-!
# Source variable-site cores versus their corridor cores

The finite neighboring-macrocell certificates lift to actual source
coordinates.  A routed variable-site prefix is bounded in its source
variable macrocell, strictly avoids every legal tile centered at a distinct
source point, and therefore strictly avoids its complete ribbon corridor.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The constructed routed variable prefix stays inside its source-variable
ribbon macrocell. -/
theorem constructedRoutedVariablePrefix_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈ constructedRoutedVariablePrefix placement entry color) :
    InRibbonMacrocell (placement.position entry.1.1) point := by
  rw [← translatedRoutedVariableSiteRoute_eq_constructedPrefix
    entry color] at member
  unfold translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨localPoint, localMember, rfl⟩
  apply inRibbonMacrocell_add_origin
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  change localPoint ∈
    translatePolyline standardThreeStrandLayout.variableOffset _ at localMember
  rw [← sourceVariableRibbonFanData_routedVariableSiteRoute
    presentation entry color] at localMember
  exact data.routedVariableSiteRoute_points_bounded
    slot active color localMember

/-- The constructed prefix has no contact with an arbitrary ribbon exit in
its owning source macrocell. -/
theorem constructedRoutedVariablePrefix_strictlyAvoids_ribbonMacrocellExit
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (direction : AxisDirection)
    (lane : WireColor) :
    RoutesStrictlyAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      [ribbonMacrocellExit
        (placement.position entry.1.1) direction lane] := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  have localAvoid :=
    data.routedVariableSiteRoute_strictlyAvoids_ribbonMacrocellExit
      slot active color direction lane
  have translatedAvoid :=
    localAvoid.translatePolyline
      (ribbonMacrocellOrigin (placement.position entry.1.1))
  rw [sourceVariableRibbonFanData_routedVariableSiteRoute
    presentation entry color] at translatedAvoid
  rw [translatedRoutedVariableSiteRoute_eq_constructedPrefix
    entry color] at translatedAvoid
  simpa [translatePolyline, ribbonMacrocellExit,
    data, slot] using translatedAvoid

/-- The constructed prefix strictly avoids every legal ribbon tile whose
source center differs from its variable center. -/
theorem constructedRoutedVariablePrefix_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (center : Cell)
    (centerNe : center ≠ placement.position entry.1.1)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (ribbonMacrocellRoute center incoming outgoing tileColor) := by
  let firstCenter := placement.position entry.1.1
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter center with
    centersEqual | centersFar | centersAdjacent
  · exact (centerNe centersEqual.symm).elim
  · exact
      routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
        (fun point member =>
          constructedRoutedVariablePrefix_points_bounded
            presentation entry color member)
        (fun point member =>
          ribbonMacrocellRoute_points_bounded
            center incoming outgoing tileColor point member)
        centersFar
  · let data := sourceVariableRibbonFanData presentation entry
    let slot := occurrenceVariableSiteSlot entry.1.2
    let active : data.SlotActive slot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
        presentation entry
    let offset := Cell.sub center firstCenter
    have centerEq : center = Cell.add firstCenter offset := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      simp [offset, Cell.add, Cell.sub]
    have localAvoid :=
      data.routedVariableSiteRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
        slot active color offset centersAdjacent
        incoming outgoing incomingGenuine outgoingGenuine
        noReverse tileColor
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have tileTranslation :
        translatePolyline (ribbonMacrocellOrigin firstCenter)
            (ribbonMacrocellRoute offset incoming outgoing tileColor) =
          ribbonMacrocellRoute center incoming outgoing tileColor := by
      unfold translatePolyline
      rw [← ribbonMacrocellRoute_add_center]
      rw [← centerEq]
    rw [tileTranslation] at translatedAvoid
    rw [sourceVariableRibbonFanData_routedVariableSiteRoute
      presentation entry color] at translatedAvoid
    rw [translatedRoutedVariableSiteRoute_eq_constructedPrefix
      entry color] at translatedAvoid
    simpa [firstCenter, data, slot] using translatedAvoid

/-- If the variable center does not reappear among the tile centers of a
corridor suffix, the constructed prefix strictly avoids that suffix. -/
theorem constructedRoutedVariablePrefix_strictlyAvoids_ribbonCorridorCore_of_start_fresh
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (previous center next : Cell)
    (rest : List Cell)
    (unitSteps :
      (previous :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (previous :: center :: next :: rest))
    (startFresh :
      placement.position entry.1.1 ∉ center :: next :: rest)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (ribbonCorridorCore tileColor
        (previous :: center :: next :: rest)) := by
  induction rest generalizing previous center next with
  | nil =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons unitSteps
      have centerNe : center ≠ placement.position entry.1.1 := by
        have fresh :
            placement.position entry.1.1 ≠ center ∧
              placement.position entry.1.1 ≠ next := by
          simpa using startFresh
        exact fresh.1.symm
      exact
        constructedRoutedVariablePrefix_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation entry color center centerNe
          (AxisDirection.between previous center)
          (AxisDirection.between center next)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          noReversal.1 tileColor
  | cons fourth rest induction =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons unitSteps
      have freshParts :
          center ≠ placement.position entry.1.1 ∧
            placement.position entry.1.1 ∉ next :: fourth :: rest := by
        have fresh :
            placement.position entry.1.1 ≠ center ∧
              placement.position entry.1.1 ∉ next :: fourth :: rest := by
          simpa using startFresh
        exact ⟨fresh.1.symm, fresh.2⟩
      have headAvoid :=
        constructedRoutedVariablePrefix_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation entry color center freshParts.1
          (AxisDirection.between previous center)
          (AxisDirection.between center next)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          noReversal.1 tileColor
      have tailAvoid :=
        induction center next fourth parts.2.2 noReversal.2
          freshParts.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 tileColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? center
          (AxisDirection.between previous center)
          (AxisDirection.between center next) tileColor)
      rw [shared]
      exact ribbonCorridorCore_head? tileColor center next fourth rest

/-- A routed variable-site prefix strictly avoids the complete ribbon
corridor of its own occurrence. -/
theorem constructedRoutedVariablePrefix_strictlyAvoids_occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesStrictlyAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  have routeLength : 2 ≤ route.length := by
    simpa [route] using occurrenceUnitSourceRoute_length planar entry
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons next rest =>
          have startEq : start = placement.position entry.1.1 := by
            have headEq :=
              occurrenceUnitSourceRoute_variableEndpoint_head?
                planar entry
            rw [show occurrenceUnitSourceRoute planar entry =
                start :: next :: rest by
              simpa [route] using routeEquation] at headEq
            exact Option.some.inj headEq
          subst start
          have actualRouteEquation :
              occurrenceUnitSourceRoute planar entry =
                placement.position entry.1.1 :: next :: rest := by
            simpa [route] using routeEquation
          cases rest with
          | nil =>
              change RoutesStrictlyAvoidEachOther _
                (ribbonCorridorCore
                  (routedRibbonLane source.erase entry color)
                  (occurrenceUnitSourceRoute planar entry))
              rw [actualRouteEquation, ribbonCorridorCore_pair]
              exact
                constructedRoutedVariablePrefix_strictlyAvoids_ribbonMacrocellExit
                  planar entry color
                  (AxisDirection.between
                    (placement.position entry.1.1) next)
                  (routedRibbonLane source.erase entry color)
          | cons third rest =>
              have unitSteps :
                  (placement.position entry.1.1 :: next :: third :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar entry
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (placement.position entry.1.1 :: next :: third :: rest) := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                  presentation.toContinuousPlanarIncidencePresentation entry
              have routeNodup :
                  (placement.position entry.1.1 :: next :: third :: rest).Nodup := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_nodup presentation entry
              have startFresh :
                  placement.position entry.1.1 ∉ next :: third :: rest :=
                (List.nodup_cons.mp routeNodup).1
              change RoutesStrictlyAvoidEachOther _
                (ribbonCorridorCore
                  (routedRibbonLane source.erase entry color)
                  (occurrenceUnitSourceRoute planar entry))
              rw [actualRouteEquation]
              exact
                constructedRoutedVariablePrefix_strictlyAvoids_ribbonCorridorCore_of_start_fresh
                  planar entry color
                  (placement.position entry.1.1) next third rest
                  unitSteps noReversal startFresh
                  (routedRibbonLane source.erase entry color)

/-- The constructed prefix avoids the joined variable stub and corridor
core, allowing only its advertised port contact with the variable stub. -/
theorem constructedRoutedVariablePrefix_avoids_variableStub_join_corridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color)) := by
  apply RoutesAvoidEachOther.join_right_of_strict_suffix
    (constructedRoutedVariablePrefix_avoids_coordinatedVariableStub
      presentation.toPlanarIncidencePresentation compatible entry color)
    (constructedRoutedVariablePrefix_strictlyAvoids_occurrenceRibbonCorridorCore
      presentation entry color)
  · exact
      (occurrenceCoordinatedRibbonVariableStub_endpoints
        presentation.toPlanarIncidencePresentation compatible
        entry color).2
  · exact
      (occurrenceRibbonCorridorCore_endpoints
        presentation.toPlanarIncidencePresentation entry color).1

/-- The same variable-stub-plus-corridor certificate in the coordinates of
any global routing using the standard constructed variable origins. -/
theorem assembledRoutedVariablePrefix_avoids_variableStub_join_corridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (routing : ThreeStrandRouting source.erase)
    (variableOriginEq :
      routing.variableOrigin =
        constructedVariableOrigin placement standardThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (assembledRoutedVariablePrefix routing entry color)
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color)) := by
  rw [assembledRoutedVariablePrefix_eq_constructed
    routing variableOriginEq entry color]
  exact
    constructedRoutedVariablePrefix_avoids_variableStub_join_corridorCore
      presentation compatible entry color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

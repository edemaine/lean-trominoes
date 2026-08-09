import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreFanSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCenterFreshness

/-!
# Source variable cores versus complete occurrence routes

Every route in a source variable core avoids every complete coordinated
occurrence-route suffix.  A source-route freshness argument handles all
interior corridor macrocells; the two-point corridor case is instead bounded
from its clause-facing macrocell.  Variable-fan contacts retain the weaker
`RoutesAvoidInteriorContacts` conclusion needed by the global continuous
planarity proof, while corridor and clause-stub contacts are excluded
strictly.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOneInThreePolarityNormalization

/-- The center of any active source variable is never an interior point of
any active occurrence's unit source route. -/
theorem variableCenter_not_mem_occurrenceUnitSourceRoute_tail_dropLast
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (owner entry : ActiveOccurrenceEntry source.erase) :
    placement.position owner.1.1 ∉
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).tail.dropLast := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  intro centerMember
  have routeNodup : route.Nodup := by
    simpa [route, planar] using
      occurrenceUnitSourceRoute_nodup presentation entry
  have notEndpoint :
      ¬RoutePointIsEndpoint route (placement.position owner.1.1) :=
    not_routePointIsEndpoint_of_mem_tail_dropLast_of_nodup
      routeNodup (by simpa [route, planar] using centerMember)
  have ownerHead :=
    occurrenceUnitSourceRoute_variableEndpoint_head? planar owner
  by_cases same : entry = owner
  · subst owner
    exact notEndpoint (Or.inl (by simpa [route, planar] using ownerHead))
  · have meetOnly :=
      occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
        presentation same
    have routeMember : placement.position owner.1.1 ∈ route := by
      apply List.mem_of_mem_tail
      exact List.mem_of_mem_dropLast
        (by simpa [route, planar] using centerMember)
    have ownerMember :
        placement.position owner.1.1 ∈
          occurrenceUnitSourceRoute planar owner :=
      List.mem_of_mem_head? ownerHead
    rcases List.mem_iff_get.mp routeMember with
      ⟨routeIndex, routePointEq⟩
    rcases List.mem_iff_get.mp ownerMember with
      ⟨ownerIndex, ownerPointEq⟩
    have endpoints := meetOnly routeIndex ownerIndex
      (routePointEq.trans ownerPointEq.symm)
    apply notEndpoint
    have endpointAtIndex :
        RoutePointIsEndpoint route (route.get routeIndex) := by
      simpa [route, planar] using endpoints.1
    rw [routePointEq] at endpointAtIndex
    exact endpointAtIndex

/-- Every route in an active source variable core strictly avoids every
occurrence's central ribbon corridor. -/
theorem constructedVariableSiteRoute_strictlyAvoids_occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (owner entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase owner.1.1)
        (sourceVariableSiteKind source.erase owner.1.1))
    (coreColor corridorColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          owner.1.1)
        ((sourceVariableSiteDrawing source.erase owner.1.1).route
          triple coreColor))
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry corridorColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  let firstCenter := placement.position owner.1.1
  have routeLength : 2 ≤ route.length := by
    simpa [route] using occurrenceUnitSourceRoute_length planar entry
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons second rest =>
          have actualRouteEquation :
              occurrenceUnitSourceRoute planar entry =
                start :: second :: rest := by
            simpa [route] using routeEquation
          cases rest with
          | nil =>
              have pairRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    [start, second] := by
                simpa using actualRouteEquation
              have unitStep :
                  AxisDirection.IsUnitAxisStep start second := by
                have steps := occurrenceUnitSourceRoute_unitSteps planar entry
                rw [pairRouteEquation] at steps
                simpa using steps
              have secondEq :
                  second = occurrenceSourceClauseTarget planar entry := by
                have endpoints := occurrenceUnitSourceRoute_endpoints planar entry
                rw [pairRouteEquation] at endpoints
                simpa [occurrenceSourceClauseTarget] using
                  Option.some.inj endpoints.2
              have centersNe : firstCenter ≠ second := by
                rw [secondEq]
                exact occurrenceSourceVariablePosition_ne_clauseTarget
                  presentation owner entry
              have separated :=
                insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
                  (firstCenter := firstCenter) (secondCenter := second)
                  (first :=
                    translatePolyline standardThreeStrandLayout.variableOffset
                      ((sourceVariableSiteDrawing source.erase owner.1.1).route
                        triple coreColor))
                  (second :=
                    occurrenceRibbonCorridorCore planar entry corridorColor)
                  (sourceVariableSiteRoute_points_in_inset_rectangle
                    source.erase owner.1.1 owner.atom_mem triple coreColor)
                  (fun point pointMember => by
                    rw [occurrenceRibbonCorridorCore,
                      pairRouteEquation] at pointMember
                    simp only [ribbonCorridorCore_pair,
                      List.mem_singleton] at pointMember
                    subst point
                    unfold ribbonCorridorCoreStart
                    rw [ribbonMacrocellExit_eq_entry_of_unitAxisStep
                      unitStep]
                    apply inRibbonMacrocell_add_origin
                    exact standardRibbonMacrocellEntry_bounded
                      (AxisDirection.between start second)
                      (routedRibbonLane source.erase entry corridorColor))
                  centersNe
              rw [translatePolyline_add] at separated
              simpa [constructedVariableOrigin, firstCenter,
                ribbonMacrocellOrigin, Cell.add, add_comm] using separated
          | cons third rest =>
              have longRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    start :: second :: third :: rest := by
                simpa using actualRouteEquation
              have unitSteps :
                  (start :: second :: third :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← longRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar entry
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (start :: second :: third :: rest) := by
                rw [← longRouteEquation]
                exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                  presentation.toContinuousPlanarIncidencePresentation entry
              have fresh :
                  firstCenter ∉ (second :: third :: rest).dropLast := by
                have sourceFresh :=
                  variableCenter_not_mem_occurrenceUnitSourceRoute_tail_dropLast
                    presentation owner entry
                rw [longRouteEquation] at sourceFresh
                simpa [firstCenter] using sourceFresh
              have separated :=
                translatedInsetRoute_strictlyAvoids_ribbonCorridorCore_of_interior_fresh
                  (firstCenter := firstCenter)
                  (first :=
                    translatePolyline standardThreeStrandLayout.variableOffset
                      ((sourceVariableSiteDrawing source.erase owner.1.1).route
                        triple coreColor))
                  (sourceVariableSiteRoute_points_in_inset_rectangle
                    source.erase owner.1.1 owner.atom_mem triple coreColor)
                  start second third rest unitSteps noReversal fresh
                  (routedRibbonLane source.erase entry corridorColor)
              rw [translatePolyline_add] at separated
              rw [occurrenceRibbonCorridorCore, longRouteEquation]
              simpa [constructedVariableOrigin, firstCenter,
                ribbonMacrocellOrigin, Cell.add, add_comm] using separated

/-- Every route in an active source variable core strictly avoids every
coordinated clause-side fan. -/
theorem constructedVariableSiteRoute_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (owner entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase owner.1.1)
        (sourceVariableSiteKind source.erase owner.1.1))
    (coreColor routeColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          owner.1.1)
        ((sourceVariableSiteDrawing source.erase owner.1.1).route
          triple coreColor))
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry routeColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position owner.1.1
  let secondCenter := occurrenceSourceClauseTarget planar entry
  have centersNe : firstCenter ≠ secondCenter :=
    occurrenceSourceVariablePosition_ne_clauseTarget
      presentation owner entry
  have separated :=
    insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
      (firstCenter := firstCenter) (secondCenter := secondCenter)
      (first :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase owner.1.1).route
            triple coreColor))
      (second :=
        occurrenceCoordinatedRibbonClauseStub planar entry routeColor)
      (sourceVariableSiteRoute_points_in_inset_rectangle
        source.erase owner.1.1 owner.atom_mem triple coreColor)
      (fun point member => by
        simpa [secondCenter, occurrenceSourceClauseTarget] using
          occurrenceCoordinatedRibbonClauseStub_points_bounded
            planar compatible entry routeColor member)
      centersNe
  rw [translatePolyline_add] at separated
  simpa [constructedVariableOrigin, firstCenter, secondCenter,
    ribbonMacrocellOrigin, Cell.add, add_comm] using separated

/-- Every route in an active source variable core avoids all segment-interior
contacts with every complete coordinated occurrence route. -/
theorem constructedVariableSiteRoute_avoids_occurrenceThreeStrandRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (owner entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase owner.1.1)
        (sourceVariableSiteKind source.erase owner.1.1))
    (coreColor routeColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          owner.1.1)
        ((sourceVariableSiteDrawing source.erase owner.1.1).route
          triple coreColor))
      (RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry routeColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let coreRoute :=
    translatePolyline
      (constructedVariableOrigin placement standardThreeStrandLayout
        owner.1.1)
      ((sourceVariableSiteDrawing source.erase owner.1.1).route
        triple coreColor)
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor :=
    occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid :
      RoutesAvoidInteriorContacts coreRoute variableStub := by
    simpa [coreRoute, variableStub, planar] using
      constructedVariableSiteRoute_avoids_occurrenceCoordinatedRibbonVariableStubInteriors
        presentation anchorsZero width normalized compatible
        owner.1.1 owner.atom_mem triple coreColor entry routeColor
  have corridorAvoid :
      RoutesAvoidInteriorContacts coreRoute corridor :=
    RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [coreRoute, corridor, planar] using
        constructedVariableSiteRoute_strictlyAvoids_occurrenceRibbonCorridorCore
          presentation owner entry triple coreColor routeColor)
  have clauseAvoid :
      RoutesAvoidInteriorContacts coreRoute clauseStub :=
    RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [coreRoute, clauseStub, planar] using
        constructedVariableSiteRoute_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
          presentation compatible owner entry triple coreColor routeColor)
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have prefixAvoid :
      RoutesAvoidInteriorContacts coreRoute
        (joinAtEndpoint variableStub corridor) :=
    variableAvoid.join_right corridorAvoid
      variableEndpoints.2 corridorEndpoints.1
  have prefixLast :
      (joinAtEndpoint variableStub corridor).getLast? =
        some (ribbonCorridorRouteEnd
          (routedRibbonLane source.erase entry routeColor)
          (occurrenceUnitSourceRoute planar entry)) :=
    joinAtEndpoint_getLast?
      variableEndpoints.2 corridorEndpoints.1 corridorEndpoints.2
  have fullAvoid :=
    prefixAvoid.join_right clauseAvoid
      prefixLast
      clauseEndpoints.1
  simpa [RibbonEndpointFanSystem.occurrenceThreeStrandRoute,
    coordinatedSourceRibbonEndpointFanSystem, coreRoute, variableStub,
    corridor, clauseStub, planar] using fullAvoid

/-- The same all-pairs variable-core certificate for the route selected by
the actual coordinated source routing. -/
theorem constructedVariableSiteRoute_avoids_coordinatedSourceRibbonRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (owner entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase owner.1.1)
        (sourceVariableSiteKind source.erase owner.1.1))
    (coreColor routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          owner.1.1)
        ((sourceVariableSiteDrawing source.erase owner.1.1).route
          triple coreColor))
      (routing.route entry routeColor) := by
  dsimp only
  rw [coordinatedSourceRibbonThreeStrandRouting_route]
  exact
    constructedVariableSiteRoute_avoids_occurrenceThreeStrandRouteInteriors
      presentation anchorsZero width normalized compatible owner entry triple
      coreColor routeColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

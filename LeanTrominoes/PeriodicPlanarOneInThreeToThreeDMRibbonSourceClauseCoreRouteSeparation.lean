import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCenterFreshness
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Source clause cores versus complete occurrence routes

The variable stub and central corridor are contact-free from every checked
clause core.  The final clause stub may meet the core, but only at its final
advertised core port.  This file composes those three facts across the two
endpoint joins that define a complete coordinated occurrence route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every checked clause core avoids every complete coordinated occurrence
route.  A common clause port is retained as a legal pair of outer endpoints. -/
theorem constructedClauseRoute_avoids_coordinatedOccurrenceThreeStrandRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry routeColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let coreRoute :=
    translatePolyline
      (constructedClauseOrigin source standardThreeStrandLayout clauseIndex)
      (X3CClauseOrthogonal.route set coreColor)
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor :=
    occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid :
      RoutesStrictlyAvoidEachOther coreRoute variableStub := by
    simpa [coreRoute, variableStub, planar] using
      constructedClauseRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub
        planar anchorsZero compatible clauseIndex indexLt set coreColor
        entry routeColor
  have corridorAvoid :
      RoutesStrictlyAvoidEachOther coreRoute corridor := by
    simpa [coreRoute, corridor, planar] using
      constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore
        presentation anchorsZero occurrences arity clauseIndex indexLt set
        coreColor entry routeColor
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther coreRoute
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
  have clauseAvoid : RoutesAvoidEachOther clauseStub coreRoute := by
    exact routesAvoidEachOther_comm (by
      simpa [coreRoute, clauseStub, planar] using
        constructedClauseRoute_avoids_occurrenceCoordinatedRibbonClauseStub
          planar compatible clauseIndex set coreColor entry routeColor)
  have clauseContacts :
      RoutesMeetOnlyAtFirstTail clauseStub coreRoute := by
    simpa [coreRoute, clauseStub, planar] using
      occurrenceCoordinatedRibbonClauseStub_meets_constructedClauseRoute_onlyAtFirstTail
        planar compatible clauseIndex set coreColor entry routeColor
  have fullAvoid :
      RoutesAvoidEachOther
        (joinAtEndpoint
          (joinAtEndpoint variableStub corridor)
          clauseStub)
        coreRoute :=
    RoutesAvoidEachOther.join_left_of_tail_contact
      prefixAvoid.symm clauseAvoid clauseContacts prefixLast clauseEndpoints.1
  apply routesAvoidEachOther_comm
  simpa [RibbonEndpointFanSystem.occurrenceThreeStrandRoute,
    coordinatedSourceRibbonEndpointFanSystem, coreRoute, variableStub,
    corridor, clauseStub, planar] using fullAvoid

/-- Every listed contact of a complete coordinated occurrence route with a
clause core occurs at the outer clause tail of the occurrence route. -/
theorem
    coordinatedOccurrenceThreeStrandRoute_meets_constructedClauseRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    RoutesMeetOnlyAtFirstTail
      (RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry routeColor)
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let coreRoute :=
    translatePolyline
      (constructedClauseOrigin source standardThreeStrandLayout clauseIndex)
      (X3CClauseOrthogonal.route set coreColor)
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor :=
    occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid :
      RoutesStrictlyAvoidEachOther coreRoute variableStub := by
    simpa [coreRoute, variableStub, planar] using
      constructedClauseRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub
        planar anchorsZero compatible clauseIndex indexLt set coreColor
        entry routeColor
  have corridorAvoid :
      RoutesStrictlyAvoidEachOther coreRoute corridor := by
    simpa [coreRoute, corridor, planar] using
      constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore
        presentation anchorsZero occurrences arity clauseIndex indexLt set
        coreColor entry routeColor
  have clauseContacts :
      RoutesMeetOnlyAtFirstTail clauseStub coreRoute := by
    simpa [coreRoute, clauseStub, planar] using
      occurrenceCoordinatedRibbonClauseStub_meets_constructedClauseRoute_onlyAtFirstTail
        planar compatible clauseIndex set coreColor entry routeColor
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have prefixLast :
      (joinAtEndpoint variableStub corridor).getLast? =
        some (ribbonCorridorRouteEnd
          (routedRibbonLane source.erase entry routeColor)
          (occurrenceUnitSourceRoute planar entry)) :=
    joinAtEndpoint_getLast?
      variableEndpoints.2 corridorEndpoints.1 corridorEndpoints.2
  intro routePoint routeMember corePoint coreMember pointsEqual
  have routeMember' :
      routePoint ∈
        joinAtEndpoint
          (joinAtEndpoint variableStub corridor) clauseStub := by
    simpa [RibbonEndpointFanSystem.occurrenceThreeStrandRoute,
      coordinatedSourceRibbonEndpointFanSystem, variableStub, corridor,
      clauseStub, planar] using routeMember
  rcases mem_joinAtEndpoint routeMember' with
    prefixMember | clauseMember
  · rcases mem_joinAtEndpoint prefixMember with
      variableMember | corridorMember
    · exact
        (variableAvoid.2.2.2
          corePoint (by simpa [coreRoute] using coreMember)
          routePoint variableMember pointsEqual.symm).elim
    · exact
        (corridorAvoid.2.2.2
          corePoint (by simpa [coreRoute] using coreMember)
          routePoint corridorMember pointsEqual.symm).elim
  · have contacts :=
      clauseContacts routePoint clauseMember corePoint
        (by simpa [coreRoute] using coreMember) pointsEqual
    have fullLast :
        (joinAtEndpoint
          (joinAtEndpoint variableStub corridor) clauseStub).getLast? =
            some routePoint :=
      joinAtEndpoint_getLast?
        prefixLast clauseEndpoints.1 contacts.1
    exact
      ⟨by simpa [RibbonEndpointFanSystem.occurrenceThreeStrandRoute,
          coordinatedSourceRibbonEndpointFanSystem, variableStub, corridor,
          clauseStub, planar] using fullLast,
        contacts.2⟩

/-- The assembled checked clause route avoids every complete occurrence
route selected by the coordinated source routing. -/
theorem assembledClauseRoute_avoids_coordinatedSourceRibbonRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledClauseRoute routing clauseIndex set coreColor)
      (routing.route entry routeColor) := by
  dsimp only
  rw [coordinatedSourceRibbonThreeStrandRouting_route]
  simpa [assembledClauseRoute, orientedIncidenceLocalRoute,
    coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting] using
    constructedClauseRoute_avoids_coordinatedOccurrenceThreeStrandRoute
      presentation anchorsZero occurrences arity width compatible clauseIndex
      indexLt set coreColor entry routeColor

/-- The route-field form of the clause-tail contact classification. -/
theorem
    coordinatedSourceRibbonRoute_meets_assembledClauseRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesMeetOnlyAtFirstTail
      (routing.route entry routeColor)
      (assembledClauseRoute routing clauseIndex set coreColor) := by
  dsimp only
  rw [coordinatedSourceRibbonThreeStrandRouting_route]
  simpa [assembledClauseRoute, orientedIncidenceLocalRoute,
    coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting] using
    coordinatedOccurrenceThreeStrandRoute_meets_constructedClauseRoute_onlyAtFirstTail
      presentation anchorsZero occurrences arity width compatible clauseIndex
      indexLt set coreColor entry routeColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

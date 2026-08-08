import LeanTrominoes.OrthogonalPolylineJoinSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanCorridorContacts

/-!
# Simplicity of the variable-fan/corridor prefix

For a source route with an interior lattice point, the variable fan has its
single advertised contact with the first corridor tile.  Duplicate freedom
makes every later tile contact-free, so endpoint joining preserves simplicity
of the whole variable-fan/corridor prefix.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A variable fan strictly avoids the corridor beginning at the second
interior center of its own duplicate-free occurrence route. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_laterRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (first next fourth : Cell)
    (rest : List Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        placement.position entry.1.1 :: first :: next :: fourth :: rest)
    (unitSteps :
      (placement.position entry.1.1 :: first :: next :: fourth :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (placement.position entry.1.1 :: first :: next :: fourth :: rest))
    (routeNodup :
      (placement.position entry.1.1 :: first :: next :: fourth :: rest).Nodup) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry color)
      (ribbonCorridorCore
        (routedRibbonLane source.erase entry color)
        (first :: next :: fourth :: rest)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let tailRoute := first :: next :: fourth :: rest
  have startNotTail :
      placement.position entry.1.1 ∉ first :: next :: fourth :: rest :=
    (List.nodup_cons.mp routeNodup).1
  have tailNodup : tailRoute.Nodup :=
    (List.nodup_cons.mp routeNodup).2
  have interiorCentersNe :
      ∀ (leading : List Cell) (previous center following : Cell)
        (remaining : List Cell),
        tailRoute = leading ++
            previous :: center :: following :: remaining →
          center ≠ placement.position entry.1.1 ∧ center ≠ first := by
    intro leading previous center following remaining equation
    have centerMember : center ∈ tailRoute := by
      rw [equation]
      simp
    have centerInternal : ¬RoutePointIsEndpoint tailRoute center :=
      routeCenter_not_endpoint_of_nodup_of_eq_append_triple
        equation tailNodup
    constructor
    · intro centerEq
      apply startNotTail
      rw [← centerEq]
      exact centerMember
    · intro centerEq
      apply centerInternal
      left
      simpa [tailRoute, centerEq]
  have parts := unitSteps_cons_cons_cons unitSteps
  exact
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
      presentation compatible entry color
      first (next :: fourth :: rest) routeEquation parts.1
      tailRoute interiorCentersNe []
      first next fourth rest rfl
      parts.2.2 noReversal.2
      (routedRibbonLane source.erase entry color)

/-- The coordinated variable fan is ordinarily separated from its complete
same-colored occurrence corridor. -/
theorem occurrenceCoordinatedRibbonVariableStub_avoids_occurrenceRibbonCorridorCore_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    RoutesAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry color)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  have routeLength : 3 ≤ route.length := by
    simpa [route, planar] using lengthGeThree
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons first remaining =>
          cases remaining with
          | nil => simp [routeEquation] at routeLength
          | cons next rest =>
              have startEq : start = placement.position entry.1.1 := by
                have headEq :=
                  occurrenceUnitSourceRoute_variableEndpoint_head? planar entry
                rw [show occurrenceUnitSourceRoute planar entry =
                    start :: first :: next :: rest by
                  simpa [route] using routeEquation] at headEq
                exact Option.some.inj headEq
              subst start
              have actualRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    placement.position entry.1.1 :: first :: next :: rest := by
                simpa [route] using routeEquation
              have unitSteps :
                  (placement.position entry.1.1 :: first :: next :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar entry
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (placement.position entry.1.1 :: first :: next :: rest) := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                  presentation.toContinuousPlanarIncidencePresentation entry
              have firstAvoid :=
                occurrenceCoordinatedRibbonVariableStub_avoids_firstRibbonMacrocellRoute
                  presentation compatible entry color first next rest
                  actualRouteEquation unitSteps noReversal
              cases rest with
              | nil =>
                  change RoutesAvoidEachOther _
                    (ribbonCorridorCore
                      (routedRibbonLane source.erase entry color)
                      (occurrenceUnitSourceRoute planar entry))
                  rw [actualRouteEquation, ribbonCorridorCore]
                  exact firstAvoid
              | cons fourth rest =>
                  have routeNodup :
                      (placement.position entry.1.1 :: first :: next ::
                        fourth :: rest).Nodup := by
                    rw [← actualRouteEquation]
                    exact occurrenceUnitSourceRoute_nodup presentation entry
                  have tailAvoid :=
                    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_laterRibbonCorridorCore
                      presentation compatible entry color first next fourth rest
                      actualRouteEquation unitSteps noReversal routeNodup
                  have parts := unitSteps_cons_cons_cons unitSteps
                  have shared :=
                    ribbonMacrocellExit_eq_entry_of_unitAxisStep
                      parts.2.1
                      (routedRibbonLane source.erase entry color)
                  have assembled := firstAvoid.join_right_of_strict_suffix tailAvoid
                    (ribbonMacrocellRoute_getLast? first
                      (AxisDirection.between
                        (placement.position entry.1.1) first)
                      (AxisDirection.between first next)
                      (routedRibbonLane source.erase entry color))
                    (by
                      rw [shared]
                      exact ribbonCorridorCore_head?
                        (routedRibbonLane source.erase entry color)
                        first next fourth rest)
                  change RoutesAvoidEachOther _
                    (ribbonCorridorCore
                      (routedRibbonLane source.erase entry color)
                      (occurrenceUnitSourceRoute planar entry))
                  rw [actualRouteEquation, ribbonCorridorCore]
                  exact assembled

/-- The advertised first boundary is the only listed point shared by the
variable fan and its complete same-colored occurrence corridor. -/
theorem occurrenceCoordinatedRibbonVariableStub_occurrenceRibbonCorridorCore_only_common_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    ∀ point,
      point ∈ occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry color →
      point ∈ occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry color →
      point = ribbonCorridorRouteStart
        (routedRibbonLane source.erase entry color)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  have routeLength : 3 ≤ route.length := by
    simpa [route, planar] using lengthGeThree
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons first remaining =>
          cases remaining with
          | nil => simp [routeEquation] at routeLength
          | cons next rest =>
              have startEq : start = placement.position entry.1.1 := by
                have headEq :=
                  occurrenceUnitSourceRoute_variableEndpoint_head? planar entry
                rw [show occurrenceUnitSourceRoute planar entry =
                    start :: first :: next :: rest by
                  simpa [route] using routeEquation] at headEq
                exact Option.some.inj headEq
              subst start
              have actualRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    placement.position entry.1.1 :: first :: next :: rest := by
                simpa [route] using routeEquation
              have unitSteps :
                  (placement.position entry.1.1 :: first :: next :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar entry
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (placement.position entry.1.1 :: first :: next :: rest) := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                  presentation.toContinuousPlanarIncidencePresentation entry
              have firstOnly :=
                occurrenceCoordinatedRibbonVariableStub_firstRibbonMacrocellRoute_only_common
                  presentation compatible entry color first next rest
                  actualRouteEquation unitSteps noReversal
              have boundaryEq :
                  ribbonMacrocellExit (placement.position entry.1.1)
                      (AxisDirection.between
                        (placement.position entry.1.1) first)
                      (routedRibbonLane source.erase entry color) =
                    ribbonCorridorRouteStart
                      (routedRibbonLane source.erase entry color)
                      (occurrenceUnitSourceRoute planar entry) := by
                rw [occurrenceRibbonCorridorRouteStart_eq planar entry color]
                simp [occurrenceSourceVariableDirection, actualRouteEquation]
              cases rest with
              | nil =>
                  intro point fanMember coreMember
                  change point ∈ ribbonCorridorCore
                    (routedRibbonLane source.erase entry color)
                    (occurrenceUnitSourceRoute planar entry) at coreMember
                  rw [actualRouteEquation, ribbonCorridorCore] at coreMember
                  exact (firstOnly point fanMember coreMember).trans boundaryEq
              | cons fourth rest =>
                  have routeNodup :
                      (placement.position entry.1.1 :: first :: next ::
                        fourth :: rest).Nodup := by
                    rw [← actualRouteEquation]
                    exact occurrenceUnitSourceRoute_nodup presentation entry
                  have tailAvoid :=
                    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_laterRibbonCorridorCore
                      presentation compatible entry color first next fourth rest
                      actualRouteEquation unitSteps noReversal routeNodup
                  intro point fanMember coreMember
                  change point ∈ ribbonCorridorCore
                    (routedRibbonLane source.erase entry color)
                    (occurrenceUnitSourceRoute planar entry) at coreMember
                  rw [actualRouteEquation, ribbonCorridorCore] at coreMember
                  rcases mem_joinAtEndpoint coreMember with
                    firstMember | tailMember
                  · exact (firstOnly point fanMember firstMember).trans boundaryEq
                  · exact (tailAvoid.2.2.2
                      point fanMember point tailMember rfl).elim

/-- Joining the coordinated variable fan to its complete occurrence
corridor preserves geometric simplicity. -/
theorem occurrenceCoordinatedRibbonVariableStub_join_corridorCore_simple_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    LocalIncidenceDrawing.RouteIsSimple
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color)) := by
  let planar := presentation.toPlanarIncidencePresentation
  apply
    (occurrenceCoordinatedRibbonVariableStub_simple
      planar compatible entry color).joinAtEndpoint_of_only_common
  · exact occurrenceRibbonCorridorCore_simple presentation entry color
  · exact
      occurrenceCoordinatedRibbonVariableStub_avoids_occurrenceRibbonCorridorCore_of_length_ge_three
        presentation compatible entry color lengthGeThree
  · exact
      (occurrenceCoordinatedRibbonVariableStub_endpoints
        planar compatible entry color).2
  · exact (occurrenceRibbonCorridorCore_endpoints planar entry color).1
  · exact
      occurrenceCoordinatedRibbonVariableStub_occurrenceRibbonCorridorCore_only_common_of_length_ge_three
        presentation compatible entry color lengthGeThree

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

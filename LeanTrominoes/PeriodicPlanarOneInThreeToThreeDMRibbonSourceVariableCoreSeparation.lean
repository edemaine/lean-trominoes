import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanMacrocellSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSeparation

/-!
# Separating coordinated variable fans from corridor cores

A variable fan can reach a neighboring corridor tile only at the first
source step on the same physical lane.  For one occurrence, distinct
semantic strands use distinct physical lanes at that join.  For unequal
occurrences, endpoint-only contact of the source routes prevents any
interior tile center from being that first neighboring point.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The first point of an occurrence's unit source route is its source
variable position. -/
theorem occurrenceUnitSourceRoute_variableEndpoint_head?
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceUnitSourceRoute presentation entry).head? =
      some (placement.position entry.1.1) := by
  let data := occurrenceSpliceData presentation entry
  have atomEq : data.tagged.1.atom = entry.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase entry.1.1 entry.1.2 data.tagged
      data.occurrenceLookup).2
  simpa [data, atomEq] using
    (occurrenceUnitSourceRoute_endpoints presentation entry).1

/-- A one-edge core is the final point of its coordinated variable fan, so
global variable-fan separation also separates it from every other strand's
variable fan. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_pairCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor)
    (secondStart secondNext : Cell)
    (secondRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second =
        [secondStart, secondNext]) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  have stubsAvoid :=
    occurrenceCoordinatedRibbonVariableStubs_strictlyAvoidEachOther
      presentation compatible different
  have endpointMember :
      ribbonCorridorRouteStart
          (routedRibbonLane source.erase second secondColor)
          (occurrenceUnitSourceRoute planar second) ∈
        occurrenceCoordinatedRibbonVariableStub
          planar second secondColor :=
    List.mem_of_getLast?
      (occurrenceCoordinatedRibbonVariableStub_endpoints
        planar compatible second secondColor).2
  have restricted := stubsAvoid.singleton_right endpointMember
  simpa [occurrenceRibbonCorridorCore, secondRouteEquation,
    ribbonCorridorRouteStart, ribbonCorridorCoreStart,
    ribbonCorridorCore, planar] using restricted

/-- A coordinated variable fan avoids one legal tile whose center is
neither its source-variable center nor its first source-route point. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first : ActiveOccurrenceEntry source.erase)
    (firstColor : WireColor)
    (firstNext : Cell)
    (firstRest : List Cell)
    (firstRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first =
        placement.position first.1.1 :: firstNext :: firstRest)
    (firstUnit :
      AxisDirection.IsUnitAxisStep
        (placement.position first.1.1) firstNext)
    (center : Cell)
    (centerNeStart : center ≠ placement.position first.1.1)
    (centerNeNext : center ≠ firstNext)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (ribbonMacrocellRoute center incoming outgoing tileColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position first.1.1
  let data := sourceVariableRibbonFanData planar first
  let slot := occurrenceVariableSiteSlot first.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      planar first
  have firstNextStep :
      firstNext = Cell.add firstCenter (data.direction slot).step := by
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_direction]
    simpa [firstCenter, planar, occurrenceSourceVariableDirection,
      firstRouteEquation] using
      AxisDirection.add_between_step_eq_of_unitAxisStep firstUnit
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter center with
    centersEqual | centersFar | centersAdjacent
  · exact (centerNeStart centersEqual.symm).elim
  · exact
      routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
        (fun point member =>
          occurrenceCoordinatedRibbonVariableStub_points_bounded
            planar compatible first firstColor member)
        (fun point member =>
          ribbonMacrocellRoute_points_bounded
            center incoming outgoing tileColor point member)
        centersFar
  · let offset := Cell.sub center firstCenter
    have centerEq : center = Cell.add firstCenter offset := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      simp [offset, Cell.add, Cell.sub]
    have offsetNe : offset ≠ (data.direction slot).step := by
      intro offsetEq
      apply centerNeNext
      calc
        center = Cell.add firstCenter offset := centerEq
        _ = Cell.add firstCenter (data.direction slot).step := by
          rw [offsetEq]
        _ = firstNext := firstNextStep.symm
    have localAvoid :=
      data.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
        (compatible.1 first) slot active firstColor
        offset centersAdjacent incoming outgoing
        incomingGenuine outgoingGenuine noReverse tileColor
        ⟨Or.inl offsetNe, Or.inl offsetNe⟩
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
    simpa [occurrenceCoordinatedRibbonVariableStub,
      planar, firstCenter, data, slot] using translatedAvoid

/-- At the first source tile, distinct physical lanes remove the sole
possible fan/tile contact. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_firstRibbonMacrocellRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (firstColor secondColor : WireColor)
    (colorsDifferent : firstColor ≠ secondColor)
    (first next : Cell)
    (rest : List Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        placement.position entry.1.1 :: first :: next :: rest)
    (unitSteps :
      (placement.position entry.1.1 :: first :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (placement.position entry.1.1 :: first :: next :: rest)) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry firstColor)
      (ribbonMacrocellRoute first
        (AxisDirection.between (placement.position entry.1.1) first)
        (AxisDirection.between first next)
        (routedRibbonLane source.erase entry secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let center := placement.position entry.1.1
  let data := sourceVariableRibbonFanData planar entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let offset := Cell.sub first center
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      planar entry
  have parts := unitSteps_cons_cons_cons unitSteps
  have directionEq :
      AxisDirection.between center first = data.direction slot := by
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_direction]
    simp [center, planar, occurrenceSourceVariableDirection,
      routeEquation]
  have offsetEq : offset = (data.direction slot).step := by
    have firstEq :=
      AxisDirection.add_between_step_eq_of_unitAxisStep parts.1
    rw [directionEq] at firstEq
    change Cell.sub first center = (data.direction slot).step
    change first = Cell.add center (data.direction slot).step at firstEq
    rw [firstEq]
    rcases center with ⟨centerX, centerY⟩
    cases direction : data.direction slot <;>
      simp [Cell.sub, Cell.add, AxisDirection.step]
  have adjacent : RibbonMacrocellOffsetAdjacent offset := by
    rw [offsetEq]
    have genuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep parts.1
    rw [directionEq] at genuine
    cases direction : data.direction slot <;>
      simp_all [RibbonMacrocellOffsetAdjacent,
        AxisDirection.IsGenuine, AxisDirection.step]
  have lanesDifferent :
      (data.kind slot).ribbonLaneForColor firstColor ≠
        routedRibbonLane source.erase entry secondColor := by
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_ribbonLaneForColor_of_same_atom
      planar entry entry rfl firstColor]
    exact (routedRibbonLane_injective source.erase entry).ne colorsDifferent
  have localAvoid :=
    data.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
      (compatible.1 entry) slot active firstColor offset adjacent
      (AxisDirection.between center first)
      (AxisDirection.between first next)
      (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
      (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
      noReversal.1
      (routedRibbonLane source.erase entry secondColor)
      ⟨Or.inr directionEq, Or.inr lanesDifferent⟩
  have translatedAvoid :=
    localAvoid.translatePolyline (ribbonMacrocellOrigin center)
  have centerEq : first = Cell.add center offset := by
    rcases center with ⟨centerX, centerY⟩
    rcases first with ⟨firstX, firstY⟩
    simp [offset, Cell.add, Cell.sub]
  have tileTranslation :
      translatePolyline (ribbonMacrocellOrigin center)
          (ribbonMacrocellRoute offset
            (AxisDirection.between center first)
            (AxisDirection.between first next)
            (routedRibbonLane source.erase entry secondColor)) =
        ribbonMacrocellRoute first
          (AxisDirection.between center first)
          (AxisDirection.between first next)
          (routedRibbonLane source.erase entry secondColor) := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center]
    rw [← centerEq]
  rw [tileTranslation] at translatedAvoid
  simpa [occurrenceCoordinatedRibbonVariableStub,
    planar, center, data, slot] using translatedAvoid

/-- If every displayed interior center of a source-route suffix differs
from a variable center and its first neighbor, the corresponding complete
corridor suffix strictly avoids that variable fan. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first : ActiveOccurrenceEntry source.erase)
    (firstColor : WireColor)
    (firstNext : Cell)
    (firstRest : List Cell)
    (firstRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first =
        placement.position first.1.1 :: firstNext :: firstRest)
    (firstUnit :
      AxisDirection.IsUnitAxisStep
        (placement.position first.1.1) firstNext)
    (secondRoute : List Cell)
    (interiorCentersNe :
      ∀ (leading : List Cell) (previous center next : Cell)
        (rest : List Cell),
        secondRoute =
            leading ++ previous :: center :: next :: rest →
          center ≠ placement.position first.1.1 ∧
            center ≠ firstNext)
    (secondLeading : List Cell)
    (secondPrevious secondCenter secondNext : Cell)
    (secondRest : List Cell)
    (secondRouteEquation :
      secondRoute =
        secondLeading ++
          secondPrevious :: secondCenter :: secondNext :: secondRest)
    (secondUnitSteps :
      (secondPrevious :: secondCenter :: secondNext :: secondRest).IsChain
        AxisDirection.IsUnitAxisStep)
    (secondNoReversal :
      SourceRouteHasNoImmediateReversal
        (secondPrevious :: secondCenter :: secondNext :: secondRest))
    (secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (ribbonCorridorCore secondColor
        (secondPrevious :: secondCenter :: secondNext :: secondRest)) := by
  induction secondRest generalizing
      secondLeading secondPrevious secondCenter secondNext with
  | nil =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons secondUnitSteps
      have centersNe :=
        interiorCentersNe secondLeading secondPrevious
          secondCenter secondNext [] secondRouteEquation
      exact
        occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation compatible first firstColor
          firstNext firstRest firstRouteEquation firstUnit
          secondCenter centersNe.1 centersNe.2
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          secondNoReversal.1 secondColor
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons secondUnitSteps
      have centersNe :=
        interiorCentersNe secondLeading secondPrevious
          secondCenter secondNext (fourth :: rest) secondRouteEquation
      have headAvoid :=
        occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          presentation compatible first firstColor
          firstNext firstRest firstRouteEquation firstUnit
          secondCenter centersNe.1 centersNe.2
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
          secondNoReversal.1 secondColor
      have tailRouteEquation :
          secondRoute =
            (secondLeading ++ [secondPrevious]) ++
              secondCenter :: secondNext :: fourth :: rest := by
        calc
          secondRoute =
              secondLeading ++ secondPrevious :: secondCenter ::
                secondNext :: fourth :: rest := secondRouteEquation
          _ =
              (secondLeading ++ [secondPrevious]) ++
                secondCenter :: secondNext :: fourth :: rest := by
            simp
      have tailAvoid :=
        tailInduction
          (secondLeading ++ [secondPrevious])
          secondCenter secondNext fourth
          tailRouteEquation parts.2.2 secondNoReversal.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 secondColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          secondColor)
      rw [shared]
      exact
        ribbonCorridorCore_head? secondColor
          secondCenter secondNext fourth rest

/-- Every coordinated variable-side stub strictly avoids the corridor core
of a different colored strand.  This is the `variableCore` obligation for
the coordinated endpoint-fan system. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  by_cases sameOccurrence : first = second
  · subst second
    have colorsDifferent : firstColor ≠ secondColor := by
      intro colorsEqual
      exact different (Prod.ext rfl colorsEqual)
    let route := occurrenceUnitSourceRoute planar first
    have routeLength : 2 ≤ route.length := by
      simpa [route] using occurrenceUnitSourceRoute_length planar first
    cases routeEquation : route with
    | nil =>
        simp [routeEquation] at routeLength
    | cons firstStart firstTail =>
        cases firstTail with
        | nil =>
            simp [routeEquation] at routeLength
        | cons firstNext firstRest =>
            have startEq :
                firstStart = placement.position first.1.1 := by
              have headEq :=
                occurrenceUnitSourceRoute_variableEndpoint_head?
                  planar first
              rw [show
                occurrenceUnitSourceRoute planar first =
                    firstStart :: firstNext :: firstRest by
                  simpa [route] using routeEquation] at headEq
              exact Option.some.inj headEq
            subst firstStart
            have actualRouteEquation :
                occurrenceUnitSourceRoute planar first =
                  placement.position first.1.1 :: firstNext :: firstRest := by
              simpa [route] using routeEquation
            cases firstRest with
            | nil =>
                exact
                  occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_pairCore
                    presentation compatible different
                    (placement.position first.1.1) firstNext
                    actualRouteEquation
            | cons third rest =>
                have unitSteps :
                    (placement.position first.1.1 :: firstNext ::
                      third :: rest).IsChain
                        AxisDirection.IsUnitAxisStep := by
                  rw [← actualRouteEquation]
                  exact occurrenceUnitSourceRoute_unitSteps planar first
                have noReversal :
                    SourceRouteHasNoImmediateReversal
                      (placement.position first.1.1 :: firstNext ::
                        third :: rest) := by
                  rw [← actualRouteEquation]
                  exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                    presentation.toContinuousPlanarIncidencePresentation first
                have headAvoid :=
                  occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_firstRibbonMacrocellRoute
                    presentation compatible first firstColor secondColor
                    colorsDifferent firstNext third rest
                    actualRouteEquation unitSteps noReversal
                cases rest with
                | nil =>
                    change RoutesStrictlyAvoidEachOther _
                      (ribbonCorridorCore
                        (routedRibbonLane source.erase first secondColor)
                        (occurrenceUnitSourceRoute planar first))
                    rw [actualRouteEquation, ribbonCorridorCore]
                    exact headAvoid
                | cons fourth rest =>
                    have routeNodup :
                        (placement.position first.1.1 :: firstNext ::
                          third :: fourth :: rest).Nodup := by
                      rw [← actualRouteEquation]
                      exact occurrenceUnitSourceRoute_nodup
                        presentation first
                    have firstCenterNotTail :
                        placement.position first.1.1 ∉
                          firstNext :: third :: fourth :: rest :=
                      (List.nodup_cons.mp routeNodup).1
                    have tailNodup :
                        (firstNext :: third :: fourth :: rest).Nodup :=
                      (List.nodup_cons.mp routeNodup).2
                    let tailRoute := firstNext :: third :: fourth :: rest
                    have interiorCentersNe :
                        ∀ (leading : List Cell)
                          (previous center next : Cell)
                          (remaining : List Cell),
                          tailRoute = leading ++
                              previous :: center :: next :: remaining →
                            center ≠ placement.position first.1.1 ∧
                              center ≠ firstNext := by
                      intro leading previous center next remaining equation
                      have centerMember : center ∈ tailRoute := by
                        rw [equation]
                        simp
                      have centerInternal :
                          ¬RoutePointIsEndpoint tailRoute center :=
                        routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                          equation tailNodup
                      constructor
                      · intro centerEq
                        apply firstCenterNotTail
                        rw [← centerEq]
                        exact centerMember
                      · intro centerEq
                        apply centerInternal
                        left
                        simpa [tailRoute, centerEq]
                    have parts := unitSteps_cons_cons_cons unitSteps
                    have tailAvoid :=
                      occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
                        presentation compatible first firstColor
                        firstNext (third :: fourth :: rest)
                        actualRouteEquation parts.1
                        tailRoute interiorCentersNe []
                        firstNext third fourth rest rfl
                        parts.2.2 noReversal.2
                        (routedRibbonLane source.erase first secondColor)
                    have shared :=
                      ribbonMacrocellExit_eq_entry_of_unitAxisStep
                        parts.2.1
                        (routedRibbonLane source.erase first secondColor)
                    have assembled :=
                      headAvoid.join_right tailAvoid
                        (ribbonMacrocellRoute_getLast? firstNext
                          (AxisDirection.between
                            (placement.position first.1.1) firstNext)
                          (AxisDirection.between firstNext third)
                          (routedRibbonLane source.erase first secondColor))
                        (by
                          rw [shared]
                          exact ribbonCorridorCore_head?
                            (routedRibbonLane source.erase first secondColor)
                            firstNext third fourth rest)
                    change RoutesStrictlyAvoidEachOther _
                      (ribbonCorridorCore
                        (routedRibbonLane source.erase first secondColor)
                        (occurrenceUnitSourceRoute planar first))
                    rw [actualRouteEquation, ribbonCorridorCore]
                    exact assembled
  · let firstRoute := occurrenceUnitSourceRoute planar first
    let secondRoute := occurrenceUnitSourceRoute planar second
    have firstLength : 2 ≤ firstRoute.length := by
      simpa [firstRoute] using occurrenceUnitSourceRoute_length planar first
    have secondLength : 2 ≤ secondRoute.length := by
      simpa [secondRoute] using occurrenceUnitSourceRoute_length planar second
    cases firstEquation : firstRoute with
    | nil =>
        simp [firstEquation] at firstLength
    | cons firstStart firstTail =>
        cases firstTail with
        | nil =>
            simp [firstEquation] at firstLength
        | cons firstNext firstRest =>
            have firstStartEq :
                firstStart = placement.position first.1.1 := by
              have headEq :=
                occurrenceUnitSourceRoute_variableEndpoint_head?
                  planar first
              rw [show
                occurrenceUnitSourceRoute planar first =
                    firstStart :: firstNext :: firstRest by
                  simpa [firstRoute] using firstEquation] at headEq
              exact Option.some.inj headEq
            subst firstStart
            have firstRouteEquation :
                occurrenceUnitSourceRoute planar first =
                  placement.position first.1.1 :: firstNext :: firstRest := by
              simpa [firstRoute] using firstEquation
            have firstUnit :
                AxisDirection.IsUnitAxisStep
                  (placement.position first.1.1) firstNext :=
              (List.isChain_cons_cons.mp (by
                rw [← firstRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar first)).1
            cases secondEquation : secondRoute with
            | nil =>
                simp [secondEquation] at secondLength
            | cons secondStart secondTail =>
                cases secondTail with
                | nil =>
                    simp [secondEquation] at secondLength
                | cons secondNext secondRest =>
                    have secondRouteEquation :
                        occurrenceUnitSourceRoute planar second =
                          secondStart :: secondNext :: secondRest := by
                      simpa [secondRoute] using secondEquation
                    cases secondRest with
                    | nil =>
                        exact
                          occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_pairCore
                            presentation compatible different
                            secondStart secondNext secondRouteEquation
                    | cons secondThird secondRest =>
                        have secondNodup : secondRoute.Nodup := by
                          simpa [secondRoute] using
                            occurrenceUnitSourceRoute_nodup presentation second
                        have meetOnly :
                            RoutesMeetOnlyAtEndpoints firstRoute secondRoute := by
                          simpa [firstRoute, secondRoute, planar] using
                            occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
                              presentation sameOccurrence
                        have firstCenterMember :
                            placement.position first.1.1 ∈ firstRoute := by
                          rw [firstEquation]
                          simp
                        have firstNextMember : firstNext ∈ firstRoute := by
                          rw [firstEquation]
                          simp
                        have interiorCentersNe :
                            ∀ (leading : List Cell)
                              (previous center next : Cell)
                              (remaining : List Cell),
                              secondRoute = leading ++
                                  previous :: center :: next :: remaining →
                                center ≠ placement.position first.1.1 ∧
                                  center ≠ firstNext := by
                          intro leading previous center next remaining equation
                          have centerMember : center ∈ secondRoute := by
                            rw [equation]
                            simp
                          have centerInternal :
                              ¬RoutePointIsEndpoint secondRoute center :=
                            routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                              equation secondNodup
                          constructor
                          · exact
                              (routePoints_ne_of_routesMeetOnlyAtEndpoints
                                meetOnly firstCenterMember centerMember
                                (Or.inr centerInternal)).symm
                          · exact
                              (routePoints_ne_of_routesMeetOnlyAtEndpoints
                                meetOnly firstNextMember centerMember
                                (Or.inr centerInternal)).symm
                        have secondUnitSteps :
                            (secondStart :: secondNext :: secondThird ::
                              secondRest).IsChain
                                AxisDirection.IsUnitAxisStep := by
                          rw [← secondRouteEquation]
                          exact occurrenceUnitSourceRoute_unitSteps planar second
                        have secondNoReversal :
                            SourceRouteHasNoImmediateReversal
                              (secondStart :: secondNext :: secondThird ::
                                secondRest) := by
                          rw [← secondRouteEquation]
                          exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                            presentation.toContinuousPlanarIncidencePresentation
                            second
                        change RoutesStrictlyAvoidEachOther _
                          (ribbonCorridorCore
                            (routedRibbonLane source.erase second secondColor)
                            (occurrenceUnitSourceRoute planar second))
                        rw [secondRouteEquation]
                        simpa [secondRoute] using
                          occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
                              presentation compatible first firstColor
                              firstNext firstRest firstRouteEquation firstUnit
                              secondRoute interiorCentersNe []
                              secondStart secondNext secondThird secondRest
                              (by simpa [secondRoute] using secondEquation)
                              secondUnitSteps secondNoReversal
                              (routedRibbonLane source.erase second secondColor)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

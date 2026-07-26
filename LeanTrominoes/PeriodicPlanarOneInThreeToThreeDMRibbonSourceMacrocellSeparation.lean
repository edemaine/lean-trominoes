import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Separating ribbon tiles inherited from separated source routes

An interior tile of one source route and an interior tile of another cannot
realize the sole endpoint contact allowed by adjacent ribbon macrocells.
Either contact would identify a neighboring source-route point with the
other route's internal center, contradicting endpoint-only source contacts.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Interior ribbon tiles selected from two endpoint-contact-separated unit
routes strictly avoid each other, for arbitrary colors. -/
theorem interiorSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    {firstPrevious firstCenter firstNext
      secondPrevious secondCenter secondNext : Cell}
    (firstCenterMember : firstCenter ∈ firstRoute)
    (firstNextMember : firstNext ∈ firstRoute)
    (secondCenterMember : secondCenter ∈ secondRoute)
    (secondNextMember : secondNext ∈ secondRoute)
    (firstCenterInternal :
      ¬RoutePointIsEndpoint firstRoute firstCenter)
    (secondCenterInternal :
      ¬RoutePointIsEndpoint secondRoute secondCenter)
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep
        firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (secondIncomingUnit :
      AxisDirection.IsUnitAxisStep
        secondPrevious secondCenter)
    (secondOutgoingUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between
          firstPrevious firstCenter).opposite)
    (secondNoReverse :
      AxisDirection.between secondCenter secondNext ≠
        (AxisDirection.between
          secondPrevious secondCenter).opposite)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      (ribbonMacrocellRoute secondCenter
        (AxisDirection.between secondPrevious secondCenter)
        (AxisDirection.between secondCenter secondNext)
        secondColor) := by
  have firstIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstIncomingUnit
  have firstOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstOutgoingUnit
  have secondIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondIncomingUnit
  have secondOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondOutgoingUnit
  have centersDifferent :
      firstCenter ≠ secondCenter :=
    routePoints_ne_of_routesMeetOnlyAtEndpoints
      meetOnly firstCenterMember secondCenterMember
      (Or.inl firstCenterInternal)
  apply
    ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne
      centersDifferent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor
  intro firstEnd secondEnd contact
  cases firstEnd <;> cases secondEnd
  · exact contact
  · rcases contact with
      ⟨offsetEq, sameOutgoing, _sameColor⟩
    have secondNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        secondOutgoingUnit
    have secondCenterEquation :
        secondCenter =
          Cell.add firstCenter
            (AxisDirection.between
              firstPrevious firstCenter).opposite.step := by
      calc
        secondCenter =
            Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
          rcases firstCenter with ⟨firstX, firstY⟩
          rcases secondCenter with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add firstCenter
              (AxisDirection.between
                firstPrevious firstCenter).opposite.step := by
          rw [offsetEq]
    have shared : firstCenter = secondNext := by
      calc
        firstCenter =
            Cell.add
              (Cell.add firstCenter
                (AxisDirection.between
                  firstPrevious firstCenter).opposite.step)
              (AxisDirection.between
                firstPrevious firstCenter).step := by
          exact
            (AxisDirection.add_opposite_step_add_step
              firstCenter firstIncomingGenuine).symm
        _ = Cell.add secondCenter
              (AxisDirection.between
                firstPrevious firstCenter).step := by
          rw [secondCenterEquation]
        _ = Cell.add secondCenter
              (AxisDirection.between
                secondCenter secondNext).step := by
          rw [sameOutgoing]
        _ = secondNext := secondNextEquation.symm
    exact
      (routePoints_ne_of_routesMeetOnlyAtEndpoints
        meetOnly firstCenterMember secondNextMember
        (Or.inl firstCenterInternal)) shared
  · rcases contact with
      ⟨offsetEq, sameIncoming, _sameColor⟩
    have firstNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        firstOutgoingUnit
    have shared : secondCenter = firstNext := by
      calc
        secondCenter =
            Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
          rcases firstCenter with ⟨firstX, firstY⟩
          rcases secondCenter with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add firstCenter
              (AxisDirection.between
                firstCenter firstNext).step := by
          rw [offsetEq]
        _ = firstNext := firstNextEquation.symm
    exact
      (routePoints_ne_of_routesMeetOnlyAtEndpoints
        meetOnly firstNextMember secondCenterMember
        (Or.inr secondCenterInternal)) shared.symm
  · exact contact

/-- The singleton core of a one-edge source route strictly avoids an
interior tile of another endpoint-contact-separated source route. -/
theorem sourceRibbonPairCore_strictlyAvoids_interiorSourceRibbonMacrocellRoute
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    {firstCenter firstNext
      secondPrevious secondCenter secondNext : Cell}
    (firstCenterMember : firstCenter ∈ firstRoute)
    (firstNextMember : firstNext ∈ firstRoute)
    (secondCenterMember : secondCenter ∈ secondRoute)
    (secondCenterInternal :
      ¬RoutePointIsEndpoint secondRoute secondCenter)
    (firstUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (secondIncomingUnit :
      AxisDirection.IsUnitAxisStep
        secondPrevious secondCenter)
    (secondOutgoingUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (secondNoReverse :
      AxisDirection.between secondCenter secondNext ≠
        (AxisDirection.between
          secondPrevious secondCenter).opposite)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      [ribbonMacrocellExit firstCenter
        (AxisDirection.between firstCenter firstNext)
        firstColor]
      (ribbonMacrocellRoute secondCenter
        (AxisDirection.between secondPrevious secondCenter)
        (AxisDirection.between secondCenter secondNext)
        secondColor) := by
  have firstDirectionGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep firstUnit
  have secondIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondIncomingUnit
  have secondOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondOutgoingUnit
  have centersDifferent :
      firstCenter ≠ secondCenter :=
    routePoints_ne_of_routesMeetOnlyAtEndpoints
      meetOnly firstCenterMember secondCenterMember
      (Or.inr secondCenterInternal)
  have fullAvoid :=
    ribbonMacrocellRoutes_avoidEachOther_of_centers_ne
      centersDifferent
      firstDirectionGenuine firstDirectionGenuine
      (AxisDirection.ne_opposite_of_isGenuine
        firstDirectionGenuine)
      secondIncomingGenuine secondOutgoingGenuine
      secondNoReverse firstColor secondColor
  have firstExitMember :
      ribbonMacrocellExit firstCenter
          (AxisDirection.between firstCenter firstNext)
          firstColor ∈
        ribbonMacrocellRoute firstCenter
          (AxisDirection.between firstCenter firstNext)
          (AxisDirection.between firstCenter firstNext)
          firstColor :=
    List.mem_of_getLast?
      (ribbonMacrocellRoute_getLast?
        firstCenter
        (AxisDirection.between firstCenter firstNext)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
  apply
    routesStrictlyAvoidEachOther_of_avoid_of_noContact
      (fullAvoid.singleton_left firstExitMember)
  intro firstPoint firstPointMember secondPoint secondPointMember equal
  have firstPointEquation :
      firstPoint =
        ribbonMacrocellExit firstCenter
          (AxisDirection.between firstCenter firstNext)
          firstColor := by
    simpa using firstPointMember
  rw [firstPointEquation] at equal
  rcases
      ribbonMacrocellCenters_eq_or_far_or_adjacent
        firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · exact (centersDifferent centersEqual).elim
  · exact
      (ne_of_inRibbonMacrocells_of_centersFar
        (ribbonMacrocellRoute_points_bounded
          firstCenter
          (AxisDirection.between firstCenter firstNext)
          (AxisDirection.between firstCenter firstNext)
          firstColor
          (ribbonMacrocellExit firstCenter
            (AxisDirection.between firstCenter firstNext)
            firstColor)
          firstExitMember)
        (ribbonMacrocellRoute_points_bounded
          secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          secondColor secondPoint secondPointMember)
        centersFar) equal
  · rcases List.mem_iff_get.mp firstExitMember with
      ⟨firstIndex, firstIndexEquation⟩
    rcases List.mem_iff_get.mp secondPointMember with
      ⟨secondIndex, secondIndexEquation⟩
    have endpoints :=
      fullAvoid.2.2.2 firstIndex secondIndex
        (firstIndexEquation.trans
          (equal.trans secondIndexEquation.symm))
    rw [firstIndexEquation, secondIndexEquation] at endpoints
    rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          secondColor secondPoint).mp endpoints.2 with
      secondEntry | secondExit
    · have contact :=
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff
          centersAdjacent
          firstDirectionGenuine firstDirectionGenuine
          (AxisDirection.ne_opposite_of_isGenuine
            firstDirectionGenuine)
          secondIncomingGenuine secondOutgoingGenuine
          secondNoReverse
          firstColor secondColor .exit .entry).mp
          (equal.trans secondEntry)
      rcases contact with
        ⟨offsetEq, _sameIncoming, _sameColor⟩
      have firstNextEquation :=
        AxisDirection.add_between_step_eq_of_unitAxisStep
          firstUnit
      have shared : secondCenter = firstNext := by
        calc
          secondCenter =
              Cell.add firstCenter
                (Cell.sub secondCenter firstCenter) := by
            rcases firstCenter with ⟨firstX, firstY⟩
            rcases secondCenter with ⟨secondX, secondY⟩
            simp [Cell.add, Cell.sub]
          _ = Cell.add firstCenter
                (AxisDirection.between
                  firstCenter firstNext).step := by
            rw [offsetEq]
          _ = firstNext := firstNextEquation.symm
      exact
        (routePoints_ne_of_routesMeetOnlyAtEndpoints
          meetOnly firstNextMember secondCenterMember
          (Or.inr secondCenterInternal)) shared.symm
    · have contact :=
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff
          centersAdjacent
          firstDirectionGenuine firstDirectionGenuine
          (AxisDirection.ne_opposite_of_isGenuine
            firstDirectionGenuine)
          secondIncomingGenuine secondOutgoingGenuine
          secondNoReverse
          firstColor secondColor .exit .exit).mp
          (equal.trans secondExit)
      exact contact

/-- An interior source-route tile also strictly avoids the singleton core
of another one-edge source route. -/
theorem interiorSourceRibbonMacrocellRoute_strictlyAvoids_sourceRibbonPairCore
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    {firstPrevious firstCenter firstNext
      secondCenter secondNext : Cell}
    (firstCenterMember : firstCenter ∈ firstRoute)
    (firstCenterInternal :
      ¬RoutePointIsEndpoint firstRoute firstCenter)
    (secondCenterMember : secondCenter ∈ secondRoute)
    (secondNextMember : secondNext ∈ secondRoute)
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep
        firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between
          firstPrevious firstCenter).opposite)
    (secondUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      [ribbonMacrocellExit secondCenter
        (AxisDirection.between secondCenter secondNext)
        secondColor] := by
  exact
    (sourceRibbonPairCore_strictlyAvoids_interiorSourceRibbonMacrocellRoute
      meetOnly.symm
      secondCenterMember secondNextMember
      firstCenterMember firstCenterInternal
      secondUnit firstIncomingUnit firstOutgoingUnit
      firstNoReverse secondColor firstColor).symm

/-- At one source center, equal ribbon exits in genuine directions must lie
on the same side of the macrocell. -/
theorem direction_eq_of_sameCenterRibbonMacrocellExits_eq
    (center : Cell)
    {firstDirection secondDirection : AxisDirection}
    (firstGenuine : firstDirection.IsGenuine)
    (secondGenuine : secondDirection.IsGenuine)
    (firstColor secondColor : WireColor)
    (equal :
      ribbonMacrocellExit center firstDirection firstColor =
        ribbonMacrocellExit center secondDirection secondColor) :
    firstDirection = secondDirection := by
  rcases center with ⟨horizontal, vertical⟩
  cases firstDirection <;> cases secondDirection <;>
    cases firstColor <;> cases secondColor <;>
    simp_all [AxisDirection.IsGenuine,
      ribbonMacrocellExit, ribbonMacrocellOrigin,
      standardRibbonMacrocellExit,
      standardRibbonMacrocellCenter,
      standardRibbonMacrocellHalfSpan,
      standardThreeStrandLayout,
      standardRibbonLaneDistance,
      AxisDirection.step, AxisDirection.rightNormal,
      Cell.add, Cell.scale]

/-- Two one-edge source-route cores are strictly separated when coincident
source centers force their outgoing directions to differ. -/
theorem sourceRibbonPairCores_strictlyAvoidEachOther
    {firstCenter firstNext secondCenter secondNext : Cell}
    (firstUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (secondUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (directionsDifferentAtSameCenter :
      firstCenter = secondCenter →
        AxisDirection.between firstCenter firstNext ≠
          AxisDirection.between secondCenter secondNext)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      [ribbonMacrocellExit firstCenter
        (AxisDirection.between firstCenter firstNext)
        firstColor]
      [ribbonMacrocellExit secondCenter
        (AxisDirection.between secondCenter secondNext)
        secondColor] := by
  have firstGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep firstUnit
  have secondGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep secondUnit
  have endpointsDifferent :
      ribbonMacrocellExit firstCenter
          (AxisDirection.between firstCenter firstNext)
          firstColor ≠
        ribbonMacrocellExit secondCenter
          (AxisDirection.between secondCenter secondNext)
          secondColor := by
    intro equal
    rcases
        ribbonMacrocellCenters_eq_or_far_or_adjacent
          firstCenter secondCenter with
      centersEqual | centersFar | centersAdjacent
    · apply directionsDifferentAtSameCenter centersEqual
      have secondGenuine' :
          (AxisDirection.between firstCenter secondNext).IsGenuine := by
        simpa [centersEqual] using secondGenuine
      have equal' :
          ribbonMacrocellExit firstCenter
                (AxisDirection.between firstCenter firstNext)
                firstColor =
            ribbonMacrocellExit firstCenter
                (AxisDirection.between firstCenter secondNext)
                secondColor := by
        simpa [centersEqual] using equal
      have directionsEqual :=
        direction_eq_of_sameCenterRibbonMacrocellExits_eq
          firstCenter firstGenuine secondGenuine'
          firstColor secondColor equal'
      simpa [centersEqual] using directionsEqual
    · have firstExitMember :
          ribbonMacrocellExit firstCenter
              (AxisDirection.between firstCenter firstNext)
              firstColor ∈
            ribbonMacrocellRoute firstCenter
              (AxisDirection.between firstCenter firstNext)
              (AxisDirection.between firstCenter firstNext)
              firstColor :=
        List.mem_of_getLast?
          (ribbonMacrocellRoute_getLast?
            firstCenter
            (AxisDirection.between firstCenter firstNext)
            (AxisDirection.between firstCenter firstNext)
            firstColor)
      have secondExitMember :
          ribbonMacrocellExit secondCenter
              (AxisDirection.between secondCenter secondNext)
              secondColor ∈
            ribbonMacrocellRoute secondCenter
              (AxisDirection.between secondCenter secondNext)
              (AxisDirection.between secondCenter secondNext)
              secondColor :=
        List.mem_of_getLast?
          (ribbonMacrocellRoute_getLast?
            secondCenter
            (AxisDirection.between secondCenter secondNext)
            (AxisDirection.between secondCenter secondNext)
            secondColor)
      exact
        (ne_of_inRibbonMacrocells_of_centersFar
          (ribbonMacrocellRoute_points_bounded
            firstCenter
            (AxisDirection.between firstCenter firstNext)
            (AxisDirection.between firstCenter firstNext)
            firstColor
            (ribbonMacrocellExit firstCenter
              (AxisDirection.between firstCenter firstNext)
              firstColor)
            firstExitMember)
          (ribbonMacrocellRoute_points_bounded
            secondCenter
            (AxisDirection.between secondCenter secondNext)
            (AxisDirection.between secondCenter secondNext)
            secondColor
            (ribbonMacrocellExit secondCenter
              (AxisDirection.between secondCenter secondNext)
              secondColor)
            secondExitMember)
          centersFar) equal
    · have contact :=
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff
          centersAdjacent
          firstGenuine firstGenuine
          (AxisDirection.ne_opposite_of_isGenuine firstGenuine)
          secondGenuine secondGenuine
          (AxisDirection.ne_opposite_of_isGenuine secondGenuine)
          firstColor secondColor .exit .exit).mp equal
      exact contact
  simp [RoutesStrictlyAvoidEachOther,
    gridPolylineSegments, endpointsDifferent]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceMacrocellSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceSeparation

/-!
# Separating corridor cores inherited from separated source routes

Every tile center in a nondegenerate corridor core is an interior point of
its complete source route.  This file retains that full-route provenance
while recursively composing tile separation across both corridor joins.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- In a duplicate-free route, the center of any displayed consecutive
triple is not either advertised endpoint of the complete route. -/
theorem routeCenter_not_endpoint_of_nodup_of_eq_append_triple
    {route leading trailing : List Cell}
    {previous center next : Cell}
    (routeEquation :
      route =
        leading ++ previous :: center :: next :: trailing)
    (nodup : route.Nodup) :
    ¬RoutePointIsEndpoint route center := by
  subst route
  have suffixNodup :
      (previous :: center :: next :: trailing).Nodup :=
    (List.nodup_append.mp nodup).2.1
  have centerNotInFollowing :
      center ∉ next :: trailing :=
    (List.nodup_cons.mp
      (List.nodup_cons.mp suffixNodup).2).1
  intro endpoint
  rcases endpoint with headEqual | lastEqual
  · cases leading with
    | nil =>
        exact
          ((List.nodup_cons.mp suffixNodup).1
            (by
              simp only [List.mem_cons]
              exact Or.inl
                (Option.some.inj
                  (by simpa using headEqual))))
    | cons leadingHead leadingTail =>
        have leadingHeadNotInTail :=
          (List.nodup_cons.mp nodup).1
        apply leadingHeadNotInTail
        simp only [List.cons_append, List.head?_cons,
          Option.some.injEq] at headEqual
        simp [headEqual]
  · cases trailing with
    | nil =>
        apply centerNotInFollowing
        simp only [List.mem_cons]
        exact Or.inl
          (Option.some.inj
            (by simpa using lastEqual)).symm
    | cons trailingHead trailingTail =>
        apply centerNotInFollowing
        exact
          List.mem_cons_of_mem next
            (List.mem_of_getLast?
              (by
                rw [List.getLast?_append_of_ne_nil
                  leading (List.cons_ne_nil _ _)] at lastEqual
                change
                  ([previous, center, next] ++
                    trailingHead :: trailingTail).getLast? =
                      some center at lastEqual
                rw [List.getLast?_append_of_ne_nil
                  [previous, center, next]
                  (List.cons_ne_nil _ _)] at lastEqual
                exact lastEqual))

/-- One interior tile of the first full source route strictly avoids a
corridor suffix whose tile centers remain interior to the second full
source route. -/
theorem interiorSourceRibbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    {firstPrevious firstCenter firstNext : Cell}
    (firstCenterMember : firstCenter ∈ firstRoute)
    (firstNextMember : firstNext ∈ firstRoute)
    (firstCenterInternal :
      ¬RoutePointIsEndpoint firstRoute firstCenter)
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep
        firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between
          firstPrevious firstCenter).opposite)
    (secondLeading : List Cell)
    (secondPrevious secondCenter secondNext : Cell)
    (secondRest : List Cell)
    (secondRouteEquation :
      secondRoute =
        secondLeading ++
          secondPrevious :: secondCenter :: secondNext :: secondRest)
    (secondNodup : secondRoute.Nodup)
    (secondUnitSteps :
      (secondPrevious :: secondCenter :: secondNext :: secondRest).IsChain
        AxisDirection.IsUnitAxisStep)
    (secondNoReversal :
      SourceRouteHasNoImmediateReversal
        (secondPrevious :: secondCenter :: secondNext :: secondRest))
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      (ribbonCorridorCore secondColor
        (secondPrevious :: secondCenter :: secondNext :: secondRest)) := by
  induction secondRest generalizing
      secondLeading secondPrevious secondCenter secondNext with
  | nil =>
      rw [ribbonCorridorCore]
      have secondParts :=
        unitSteps_cons_cons_cons secondUnitSteps
      apply
        interiorSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
          meetOnly
          firstCenterMember firstNextMember
          (by
            rw [secondRouteEquation]
            simp)
          (by
            rw [secondRouteEquation]
            simp)
          firstCenterInternal
          (routeCenter_not_endpoint_of_nodup_of_eq_append_triple
            secondRouteEquation secondNodup)
          firstIncomingUnit firstOutgoingUnit
          secondParts.1 secondParts.2.1
          firstNoReverse secondNoReversal.1
          firstColor secondColor
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have secondParts :=
        unitSteps_cons_cons_cons secondUnitSteps
      have headAvoid :
          RoutesStrictlyAvoidEachOther
            (ribbonMacrocellRoute firstCenter
              (AxisDirection.between firstPrevious firstCenter)
              (AxisDirection.between firstCenter firstNext)
              firstColor)
            (ribbonMacrocellRoute secondCenter
              (AxisDirection.between secondPrevious secondCenter)
              (AxisDirection.between secondCenter secondNext)
              secondColor) := by
        apply
          interiorSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
            meetOnly
            firstCenterMember firstNextMember
            (by
              rw [secondRouteEquation]
              simp)
            (by
              rw [secondRouteEquation]
              simp)
            firstCenterInternal
            (routeCenter_not_endpoint_of_nodup_of_eq_append_triple
              secondRouteEquation secondNodup)
            firstIncomingUnit firstOutgoingUnit
            secondParts.1 secondParts.2.1
            firstNoReverse secondNoReversal.1
            firstColor secondColor
      have tailRouteEquation :
          secondRoute =
            (secondLeading ++ [secondPrevious]) ++
              secondCenter :: secondNext :: fourth :: rest := by
        calc
          secondRoute =
              secondLeading ++
                secondPrevious :: secondCenter :: secondNext ::
                  fourth :: rest :=
            secondRouteEquation
          _ =
              (secondLeading ++ [secondPrevious]) ++
                secondCenter :: secondNext :: fourth :: rest := by
            simp
      have tailAvoid :=
        tailInduction
          (secondLeading ++ [secondPrevious])
          secondCenter secondNext fourth
          tailRouteEquation secondParts.2.2
          secondNoReversal.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          secondParts.2.1 secondColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          secondColor)
      rw [shared]
      exact
        ribbonCorridorCore_head? secondColor
          secondCenter secondNext fourth rest

/-- Corridor suffixes from two duplicate-free endpoint-separated complete
source routes strictly avoid each other.  Both suffixes begin with a
displayed consecutive triple of their corresponding complete route. -/
theorem sourceRibbonCorridorCores_strictlyAvoidEachOther_of_append_triples
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    (firstNodup : firstRoute.Nodup)
    (secondNodup : secondRoute.Nodup)
    (firstLeading : List Cell)
    (firstPrevious firstCenter firstNext : Cell)
    (firstRest : List Cell)
    (firstRouteEquation :
      firstRoute =
        firstLeading ++
          firstPrevious :: firstCenter :: firstNext :: firstRest)
    (firstUnitSteps :
      (firstPrevious :: firstCenter :: firstNext :: firstRest).IsChain
        AxisDirection.IsUnitAxisStep)
    (firstNoReversal :
      SourceRouteHasNoImmediateReversal
        (firstPrevious :: firstCenter :: firstNext :: firstRest))
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
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonCorridorCore firstColor
        (firstPrevious :: firstCenter :: firstNext :: firstRest))
      (ribbonCorridorCore secondColor
        (secondPrevious :: secondCenter :: secondNext :: secondRest)) := by
  induction firstRest generalizing
      firstLeading firstPrevious firstCenter firstNext with
  | nil =>
      rw [ribbonCorridorCore]
      have firstParts :=
        unitSteps_cons_cons_cons firstUnitSteps
      exact
        interiorSourceRibbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
          meetOnly
          (by
            rw [firstRouteEquation]
            simp)
          (by
            rw [firstRouteEquation]
            simp)
          (routeCenter_not_endpoint_of_nodup_of_eq_append_triple
            firstRouteEquation firstNodup)
          firstParts.1 firstParts.2.1 firstNoReversal.1
          secondLeading secondPrevious secondCenter secondNext secondRest
          secondRouteEquation secondNodup
          secondUnitSteps secondNoReversal
          firstColor secondColor
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have firstParts :=
        unitSteps_cons_cons_cons firstUnitSteps
      have headAvoid :=
        interiorSourceRibbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
          meetOnly
          (by
            rw [firstRouteEquation]
            simp)
          (by
            rw [firstRouteEquation]
            simp)
          (routeCenter_not_endpoint_of_nodup_of_eq_append_triple
            firstRouteEquation firstNodup)
          firstParts.1 firstParts.2.1 firstNoReversal.1
          secondLeading secondPrevious secondCenter secondNext secondRest
          secondRouteEquation secondNodup
          secondUnitSteps secondNoReversal
          firstColor secondColor
      have tailRouteEquation :
          firstRoute =
            (firstLeading ++ [firstPrevious]) ++
              firstCenter :: firstNext :: fourth :: rest := by
        calc
          firstRoute =
              firstLeading ++
                firstPrevious :: firstCenter :: firstNext ::
                  fourth :: rest :=
            firstRouteEquation
          _ =
              (firstLeading ++ [firstPrevious]) ++
                firstCenter :: firstNext :: fourth :: rest := by
            simp
      have tailAvoid :=
        tailInduction
          (firstLeading ++ [firstPrevious])
          firstCenter firstNext fourth
          tailRouteEquation firstParts.2.2 firstNoReversal.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          firstParts.2.1 firstColor
      apply headAvoid.join_left tailAvoid
        (ribbonMacrocellRoute_getLast? firstCenter
          (AxisDirection.between firstPrevious firstCenter)
          (AxisDirection.between firstCenter firstNext)
          firstColor)
      rw [shared]
      exact
        ribbonCorridorCore_head? firstColor
          firstCenter firstNext fourth rest

/-- Complete source routes of length at least three induce strictly separated
corridor cores whenever they are duplicate-free, unit-step,
no-immediate-reversal, and meet only at advertised endpoints. -/
theorem sourceRibbonCorridorCores_strictlyAvoidEachOther
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    (firstNodup : firstRoute.Nodup)
    (secondNodup : secondRoute.Nodup)
    (firstLength : 3 ≤ firstRoute.length)
    (secondLength : 3 ≤ secondRoute.length)
    (firstUnitSteps :
      firstRoute.IsChain AxisDirection.IsUnitAxisStep)
    (secondUnitSteps :
      secondRoute.IsChain AxisDirection.IsUnitAxisStep)
    (firstNoReversal :
      SourceRouteHasNoImmediateReversal firstRoute)
    (secondNoReversal :
      SourceRouteHasNoImmediateReversal secondRoute)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonCorridorCore firstColor firstRoute)
      (ribbonCorridorCore secondColor secondRoute) := by
  cases firstRoute with
  | nil =>
      simp at firstLength
  | cons firstPrevious firstTail =>
      cases firstTail with
      | nil =>
          simp at firstLength
      | cons firstCenter firstTail =>
          cases firstTail with
          | nil =>
              simp at firstLength
          | cons firstNext firstRest =>
              cases secondRoute with
              | nil =>
                  simp at secondLength
              | cons secondPrevious secondTail =>
                  cases secondTail with
                  | nil =>
                      simp at secondLength
                  | cons secondCenter secondTail =>
                      cases secondTail with
                      | nil =>
                          simp at secondLength
                      | cons secondNext secondRest =>
                          exact
                            sourceRibbonCorridorCores_strictlyAvoidEachOther_of_append_triples
                              meetOnly firstNodup secondNodup
                              [] firstPrevious firstCenter firstNext firstRest
                              rfl firstUnitSteps firstNoReversal
                              [] secondPrevious secondCenter secondNext secondRest
                              rfl secondUnitSteps secondNoReversal
                              firstColor secondColor

/-- Unequal active occurrences whose unit source routes each contain an
interior point have strictly separated colored corridor cores, independently
of the two selected colors. -/
theorem occurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation second secondColor) := by
  apply
    sourceRibbonCorridorCores_strictlyAvoidEachOther
      (occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
        presentation different)
      (occurrenceUnitSourceRoute_nodup presentation first)
      (occurrenceUnitSourceRoute_nodup presentation second)
      firstLength secondLength
      (occurrenceUnitSourceRoute_unitSteps
        presentation.toPlanarIncidencePresentation first)
      (occurrenceUnitSourceRoute_unitSteps
        presentation.toPlanarIncidencePresentation second)
      (occurrenceUnitSourceRoute_hasNoImmediateReversal
        presentation.toContinuousPlanarIncidencePresentation first)
      (occurrenceUnitSourceRoute_hasNoImmediateReversal
        presentation.toContinuousPlanarIncidencePresentation second)
      firstColor secondColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

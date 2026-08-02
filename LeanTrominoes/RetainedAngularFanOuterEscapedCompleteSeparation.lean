import LeanTrominoes.RetainedAngularFanOuterEscapedCrossSeparation
import LeanTrominoes.RetainedAngularFanOuterMixedRadialSeparation

/-!
# Separation of complete escaped outer fan routes

Complete fan routes join a radial piece to a finite local adapter.  The
escaped radial/radial and radial/local theorems therefore combine with the
existing local/local theorem to cover escaped/escaped routes and both mixed
escaped/ordinary orders.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Four component-pair separation theorems assemble across two endpoint
joins. -/
private theorem joinedRoutes_strictlyAvoid_of_components
    {firstRadial firstLocal secondRadial secondLocal : List Cell}
    {firstBoundary secondBoundary : Cell}
    (radialRadial :
      RoutesStrictlyAvoidEachOther firstRadial secondRadial)
    (radialLocal :
      RoutesStrictlyAvoidEachOther firstRadial secondLocal)
    (localRadial :
      RoutesStrictlyAvoidEachOther firstLocal secondRadial)
    (localLocal :
      RoutesStrictlyAvoidEachOther firstLocal secondLocal)
    (firstRadialLast :
      firstRadial.getLast? = some firstBoundary)
    (firstLocalHead :
      firstLocal.head? = some firstBoundary)
    (secondRadialLast :
      secondRadial.getLast? = some secondBoundary)
    (secondLocalHead :
      secondLocal.head? = some secondBoundary) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint firstRadial firstLocal)
      (joinAtEndpoint secondRadial secondLocal) := by
  have firstCompleteAvoidRadial :=
    radialRadial.join_left localRadial
      firstRadialLast firstLocalHead
  have firstCompleteAvoidLocal :=
    radialLocal.join_left localLocal
      firstRadialLast firstLocalHead
  exact firstCompleteAvoidRadial.join_right
    firstCompleteAvoidLocal secondRadialLast secondLocalHead

/-- Complete escaped routes in strictly ordered directions and occurrence
slots are strictly separated. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (slotsLt : firstSlot.val < secondSlot.val)
    (firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (firstDirection, firstLength))
    (secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (secondDirection, secondLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        center (secondDirection, secondLength) secondSlot) := by
  have directionsLe := Nat.le_of_lt directionsLt
  have firstEscapeFits := Nat.le_of_lt firstEscapeStrict
  have secondEscapeFits := Nat.le_of_lt secondEscapeStrict
  exact joinedRoutes_strictlyAvoid_of_components
    (retainedTerminalFanOuterEscapedRadialRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection firstLength secondLength
      firstSlot secondSlot directionsLt firstLengthPositive
      secondLengthPositive slotsLt firstEscapeFits secondEscapeFits)
    (retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_laterLocal
      center (firstDirection, firstLength) firstSlot secondSlot
      secondDirection firstLengthPositive firstEscapeStrict
      directionsLe slotsLt)
    (retainedTerminalFanOuterLocal_strictlyAvoid_laterEscapedRadialRoute
      center firstDirection (secondDirection, secondLength)
      firstSlot secondSlot secondLengthPositive secondEscapeStrict
      directionsLe slotsLt)
    (retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
      center firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center (firstDirection, firstLength) firstSlot
      firstLengthPositive firstEscapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center firstDirection firstSlot)
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center (secondDirection, secondLength) secondSlot
      secondLengthPositive secondEscapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center secondDirection secondSlot)

/-- A complete escaped route in an earlier direction strictly avoids a
complete ordinary route in a later direction and occurrence slot. -/
theorem
    retainedTerminalFanOuterEscapedOrdinaryCompleteRoutes_strictlyAvoid_of_direction_lt
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (secondRadialPositive :
      0 <
        retainedTerminalFanOuterRadialLength
          (secondDirection, secondLength))
    (slotsLt : firstSlot.val < secondSlot.val)
    (firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (firstDirection, firstLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        center (secondDirection, secondLength) secondSlot) := by
  have directionsLe := Nat.le_of_lt directionsLt
  have firstEscapeFits := Nat.le_of_lt firstEscapeStrict
  exact joinedRoutes_strictlyAvoid_of_components
    (retainedTerminalFanOuterEscapedOrdinaryRadialRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection firstLength secondLength
      firstSlot secondSlot directionsLt firstLengthPositive
      secondLengthPositive slotsLt firstEscapeFits)
    (retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_laterLocal
      center (firstDirection, firstLength) firstSlot secondSlot
      secondDirection firstLengthPositive firstEscapeStrict
      directionsLe slotsLt)
    (retainedTerminalFanOuterLocal_strictlyAvoid_laterRadialRoute_of_positive
      center firstDirection (secondDirection, secondLength)
      firstSlot secondSlot secondRadialPositive directionsLe slotsLt)
    (retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
      center firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center (firstDirection, firstLength) firstSlot
      firstLengthPositive firstEscapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center firstDirection firstSlot)
    (retainedTerminalFanOuterRadialRoute_getLast?
      center (secondDirection, secondLength) secondSlot
      secondLengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center secondDirection secondSlot)

/-- A complete ordinary route in an earlier direction strictly avoids a
complete escaped route in a later direction and occurrence slot. -/
theorem
    retainedTerminalFanOuterOrdinaryEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (firstRadialPositive :
      0 <
        retainedTerminalFanOuterRadialLength
          (firstDirection, firstLength))
    (slotsLt : firstSlot.val < secondSlot.val)
    (secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (secondDirection, secondLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        center (secondDirection, secondLength) secondSlot) := by
  have directionsLe := Nat.le_of_lt directionsLt
  have secondEscapeFits := Nat.le_of_lt secondEscapeStrict
  exact joinedRoutes_strictlyAvoid_of_components
    (retainedTerminalFanOuterOrdinaryEscapedRadialRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection firstLength secondLength
      firstSlot secondSlot directionsLt firstLengthPositive
      secondLengthPositive slotsLt secondEscapeFits)
    (retainedTerminalFanOuterRadialRoute_strictlyAvoid_laterLocal_of_positive
      center (firstDirection, firstLength) firstSlot secondSlot
      secondDirection firstRadialPositive directionsLe slotsLt)
    (retainedTerminalFanOuterLocal_strictlyAvoid_laterEscapedRadialRoute
      center firstDirection (secondDirection, secondLength)
      firstSlot secondSlot secondLengthPositive secondEscapeStrict
      directionsLe slotsLt)
    (retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
      center firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    (retainedTerminalFanOuterRadialRoute_getLast?
      center (firstDirection, firstLength) firstSlot
      firstLengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center firstDirection firstSlot)
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center (secondDirection, secondLength) secondSlot
      secondLengthPositive secondEscapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center secondDirection secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

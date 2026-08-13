/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedRadialSeparation

/-!
# Separation of escaped and ordinary radial routes

The exact escaped-route half-plane bounds use the same normals and
thresholds as ordinary radial routes.  They therefore combine directly to
separate the two mixed route families in either order.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- An escaped radial route in an earlier direction strictly avoids an
ordinary radial route in a later direction and later occurrence slot. -/
theorem
    retainedTerminalFanOuterEscapedOrdinaryRadialRoutes_strictlyAvoid_of_direction_lt
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
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (firstDirection, firstLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center (secondDirection, secondLength) secondSlot) := by
  have firstSlotLtSeven : firstSlot.val < 7 := by
    have secondSlotLt := secondSlot.isLt
    omega
  have secondSlotPositive : 0 < secondSlot.val := by
    omega
  exact routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterRadialSeparatorNormal
      firstDirection secondDirection)
    (Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        center +
      retainedTerminalFanOuterRadialSeparatorBound
        firstDirection secondDirection)
    (retainedTerminalFanOuterEscapedRadialRoute_linear_upper
      center firstDirection secondDirection firstLength firstSlot
      directionsLt firstLengthPositive firstSlotLtSeven
      firstEscapeFits)
    (retainedTerminalFanOuterRadialRoute_linear_lower
      center firstDirection secondDirection secondLength secondSlot
      directionsLt secondLengthPositive secondSlotPositive)

/-- An ordinary radial route in an earlier direction strictly avoids an
escaped radial route in a later direction and later occurrence slot. -/
theorem
    retainedTerminalFanOuterOrdinaryEscapedRadialRoutes_strictlyAvoid_of_direction_lt
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
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (secondDirection, secondLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterEscapedRadialRoute
        center (secondDirection, secondLength) secondSlot) := by
  have firstSlotLtSeven : firstSlot.val < 7 := by
    have secondSlotLt := secondSlot.isLt
    omega
  have secondSlotPositive : 0 < secondSlot.val := by
    omega
  exact routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterRadialSeparatorNormal
      firstDirection secondDirection)
    (Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        center +
      retainedTerminalFanOuterRadialSeparatorBound
        firstDirection secondDirection)
    (retainedTerminalFanOuterRadialRoute_linear_upper
      center firstDirection secondDirection firstLength firstSlot
      directionsLt firstLengthPositive firstSlotLtSeven)
    (retainedTerminalFanOuterEscapedRadialRoute_linear_lower
      center firstDirection secondDirection secondLength secondSlot
      directionsLt secondLengthPositive secondSlotPositive
      secondEscapeFits)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

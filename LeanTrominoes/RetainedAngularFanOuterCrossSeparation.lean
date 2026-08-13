/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialDecomposition

/-!
# Cross-separation of radial and local fan routes

The complete source-to-fan routes join an exterior radial lane to a finite
local adapter.  This file proves the two cross-separation statements needed
for pairwise separation of those joins.

Positive radial routes use their explicit final-block decomposition.  For a
blocked raster that decomposition is exact; for a cardinal raster strict
separation is transported through the certified collinear coarsening.
Length-one compass terminals are the only zero-block case and use the finite
certificates for their tangential lane shifts.  Duplicate-free terminal
profiles exclude the sole bad local-before-zero combination.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A positive earlier radial route strictly avoids a later
order-compatible local route. -/
theorem retainedTerminalFanOuterRadialRoute_strictlyAvoid_laterLocal_of_positive
    (center : Cell)
    (firstTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (secondDirection : RetainedTerminalDirection)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal)
    (directionsLe :
      firstTerminal.1.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  have splitAvoid :=
    splitRadialRoute_strictlyAvoid_laterLocal
      center firstTerminal firstSlot secondSlot secondDirection
      radialPositive directionsLe slotsLt
  by_cases blocked : firstTerminal.1.usesBlockedRaster
  · rw [radialRoute_eq_split_of_usesBlockedRaster
      center firstTerminal firstSlot radialPositive blocked]
    exact splitAvoid
  · rcases radialRoute_direct_coarsening
      center firstTerminal firstSlot radialPositive blocked with
      ⟨leading, first, middle, finish,
        splitEq, radialEq, leadingLast, middleInterior⟩
    rw [splitEq] at splitAvoid
    rw [radialEq]
    exact splitAvoid.coarsen_middle_after_join_left
      leadingLast middleInterior

/-- An earlier local route strictly avoids a positive later
order-compatible radial route. -/
theorem retainedTerminalFanOuterLocal_strictlyAvoid_laterRadialRoute_of_positive
    (center : Cell)
    (firstDirection : RetainedTerminalDirection)
    (secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal)
    (directionsLe :
      firstDirection.angularRank ≤ secondTerminal.1.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center secondTerminal secondSlot) := by
  have splitAvoid :=
    local_strictlyAvoid_laterSplitRadialRoute
      center firstDirection secondTerminal firstSlot secondSlot
      radialPositive directionsLe slotsLt
  by_cases blocked : secondTerminal.1.usesBlockedRaster
  · rw [radialRoute_eq_split_of_usesBlockedRaster
      center secondTerminal secondSlot radialPositive blocked]
    exact splitAvoid
  · rcases radialRoute_direct_coarsening
      center secondTerminal secondSlot radialPositive blocked with
      ⟨leading, first, middle, finish,
        splitEq, radialEq, leadingLast, middleInterior⟩
    rw [splitEq] at splitAvoid
    rw [radialEq]
    exact splitAvoid.coarsen_middle_after_join_right
      leadingLast middleInterior

/-- Ordered successful profile lookups inherit the profile's nondecreasing
angular-rank order. -/
theorem RetainedAngularTerminalProfile.directionRank_le_of_lookups
    (profile : RetainedAngularTerminalProfile)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLookup :
      profile.terminals[firstSlot.val]? = some firstTerminal)
    (secondLookup :
      profile.terminals[secondSlot.val]? = some secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val) :
    firstTerminal.1.angularRank ≤ secondTerminal.1.angularRank := by
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstLt, firstEq⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondLt, secondEq⟩
  have ordered :=
    (List.pairwise_iff_getElem.mp profile.rankSorted)
      firstSlot.val secondSlot.val
      firstLt secondLt slotsLt
  simpa [firstEq, secondEq] using ordered

/-- Equal-direction successful lookups in a duplicate-free profile have
strictly increasing radial lengths. -/
theorem RetainedAngularTerminalProfile.length_lt_of_lookups_of_direction_eq
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLookup :
      profile.terminals[firstSlot.val]? = some firstTerminal)
    (secondLookup :
      profile.terminals[secondSlot.val]? = some secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsEqual : firstTerminal.1 = secondTerminal.1) :
    firstTerminal.2 < secondTerminal.2 := by
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstLt, firstEq⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondLt, secondEq⟩
  have concreteDirectionsEqual :
      (profile.terminals[firstSlot.val]'firstLt).1 =
        (profile.terminals[secondSlot.val]'secondLt).1 := by
    simpa [firstEq, secondEq] using directionsEqual
  have lengthsLt :=
    profile.length_lt_of_lt_of_direction_eq distinct
      firstSlot.val secondSlot.val
      firstLt secondLt slotsLt concreteDirectionsEqual
  simpa [firstEq, secondEq] using lengthsLt

/-- The radial route selected by an earlier profile slot strictly avoids
the local route selected by a later slot. -/
theorem RetainedAngularTerminalProfile.outerRadialRoute_strictlyAvoid_laterLocal
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLookup :
      profile.terminals[firstSlot.val]? = some firstTerminal)
    (secondLookup :
      profile.terminals[secondSlot.val]? = some secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondTerminal.1 secondSlot) := by
  have firstLengthPositive :=
    profile.length_positive_of_lookup
      firstSlot firstTerminal firstLookup
  have directionsLe :=
    profile.directionRank_le_of_lookups
      firstSlot secondSlot firstTerminal secondTerminal
      firstLookup secondLookup slotsLt
  by_cases radialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal
  · exact
      retainedTerminalFanOuterRadialRoute_strictlyAvoid_laterLocal_of_positive
        center firstTerminal firstSlot secondSlot secondTerminal.1
        radialPositive directionsLe slotsLt
  · have radialZero :
        retainedTerminalFanOuterRadialLength firstTerminal = 0 := by
      omega
    rcases
        (retainedTerminalFanOuterRadialLength_eq_zero_iff_of_positive
          firstTerminal firstLengthPositive).mp radialZero with
      ⟨port, terminalEq⟩
    rw [terminalEq,
      retainedTerminalFanOuterRadialRoute_eq_zeroRadialRouteAt]
    exact
      retainedTerminalFanOuterZeroRadialRouteAt_strictlyAvoid_laterLocal
        center (.compass port) secondTerminal.1 firstSlot secondSlot
        (by simpa [terminalEq] using directionsLe) slotsLt

/-- The local route selected by an earlier slot strictly avoids the radial
route selected by a later slot in a duplicate-free profile. -/
theorem RetainedAngularTerminalProfile.outerLocal_strictlyAvoid_laterRadialRoute
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (center : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLookup :
      profile.terminals[firstSlot.val]? = some firstTerminal)
    (secondLookup :
      profile.terminals[secondSlot.val]? = some secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstTerminal.1 firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center secondTerminal secondSlot) := by
  have secondLengthPositive :=
    profile.length_positive_of_lookup
      secondSlot secondTerminal secondLookup
  have directionsLe :=
    profile.directionRank_le_of_lookups
      firstSlot secondSlot firstTerminal secondTerminal
      firstLookup secondLookup slotsLt
  by_cases radialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal
  · exact
      retainedTerminalFanOuterLocal_strictlyAvoid_laterRadialRoute_of_positive
        center firstTerminal.1 secondTerminal firstSlot secondSlot
        radialPositive directionsLe slotsLt
  · have radialZero :
        retainedTerminalFanOuterRadialLength secondTerminal = 0 := by
      omega
    rcases
        (retainedTerminalFanOuterRadialLength_eq_zero_iff_of_positive
          secondTerminal secondLengthPositive).mp radialZero with
      ⟨port, terminalEq⟩
    have directionsNe :
        firstTerminal.1 ≠ secondTerminal.1 := by
      intro directionsEqual
      have lengthsLt :=
        profile.length_lt_of_lookups_of_direction_eq
          distinct firstSlot secondSlot firstTerminal secondTerminal
          firstLookup secondLookup slotsLt directionsEqual
      rw [terminalEq] at lengthsLt
      have firstLengthPositive :=
        profile.length_positive_of_lookup
          firstSlot firstTerminal firstLookup
      omega
    rw [terminalEq,
      retainedTerminalFanOuterRadialRoute_eq_zeroRadialRouteAt]
    exact
      retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterZeroRadialRoute
        center firstTerminal.1 (.compass port) firstSlot secondSlot
        (by simpa [terminalEq] using directionsNe)
        (by simpa [terminalEq] using directionsLe) slotsLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes

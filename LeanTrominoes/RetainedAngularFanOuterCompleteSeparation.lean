/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterCrossSeparation

/-!
# Separation of complete retained outer fan routes

Each complete route is the endpoint join of its unbounded radial lane and
its finite local adapter.  Pairwise separation follows by combining the four
component pairs: radial/radial, radial/local, local/radial, and local/local.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Complete outer routes selected by two ordered active slots of a
duplicate-free profile are strictly separated. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_strictlyAvoid
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
      (retainedTerminalFanOuterCompleteRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        center secondTerminal secondSlot) := by
  have directionsLe :=
    profile.directionRank_le_of_lookups
      firstSlot secondSlot firstTerminal secondTerminal
      firstLookup secondLookup slotsLt
  have radialAvoidRadial :=
    profile.outerRadialRoutes_strictlyAvoid
      distinct center firstSlot secondSlot
      firstTerminal secondTerminal firstLookup secondLookup slotsLt
  have radialAvoidLocal :=
    profile.outerRadialRoute_strictlyAvoid_laterLocal
      center firstSlot secondSlot firstTerminal secondTerminal
      firstLookup secondLookup slotsLt
  have localAvoidRadial :=
    profile.outerLocal_strictlyAvoid_laterRadialRoute
      distinct center firstSlot secondSlot firstTerminal secondTerminal
      firstLookup secondLookup slotsLt
  have localAvoidLocal :=
    retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
      center firstTerminal.1 secondTerminal.1
      firstSlot secondSlot directionsLe slotsLt
  have firstLengthPositive :=
    profile.length_positive_of_lookup
      firstSlot firstTerminal firstLookup
  have secondLengthPositive :=
    profile.length_positive_of_lookup
      secondSlot secondTerminal secondLookup
  have completeFirstAvoidRadial :=
    radialAvoidRadial.join_left localAvoidRadial
      (retainedTerminalFanOuterRadialRoute_getLast?
        center firstTerminal firstSlot firstLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center firstTerminal.1 firstSlot)
  have completeFirstAvoidLocal :=
    radialAvoidLocal.join_left localAvoidLocal
      (retainedTerminalFanOuterRadialRoute_getLast?
        center firstTerminal firstSlot firstLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center firstTerminal.1 firstSlot)
  exact completeFirstAvoidRadial.join_right
    completeFirstAvoidLocal
    (retainedTerminalFanOuterRadialRoute_getLast?
      center secondTerminal secondSlot secondLengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center secondTerminal.1 secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

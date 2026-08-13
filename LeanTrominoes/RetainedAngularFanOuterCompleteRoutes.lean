/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterLocalRoutes
import LeanTrominoes.RetainedAngularTerminalSlotLookup

/-!
# Complete retained source-to-Figure-7 fan routes

The outer radial route ends at the exact radius-288 lane port where the
positioned finite local adapter begins.  This file joins the two pieces for
one positive retained terminal datum, packages optional routes for a
length-aware terminal profile, and connects genuine source occurrences to
their selected routes.

Pairwise separation of the unbounded radial pieces is deliberately kept
separate from this endpoint-and-orthogonality splice.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Complete route from one scaled retained source gate, through its
radius-288 lane and finite fan adapter, to the matching refined Figure 7
boundary site. -/
def retainedTerminalFanOuterCompleteRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterRadialRoute center terminal slot)
    (retainedTerminalFanOuterLocalRouteAt
      center terminal.1 slot)

/-- A complete route begins at the exact outer-adapter gate. -/
@[simp]
theorem retainedTerminalFanOuterCompleteRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterCompleteRoute
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterRadialRoute_head?
      center terminal slot)

/-- For a positive terminal datum, a complete route ends at the exact
positioned Figure 7 boundary site for its occurrence slot. -/
@[simp]
theorem retainedTerminalFanOuterCompleteRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    (retainedTerminalFanOuterCompleteRoute
      center terminal slot).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanOuterRadialRoute_getLast?
      center terminal slot lengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center terminal.1 slot)
    (retainedTerminalFanOuterLocalRouteAt_getLast?
      center terminal.1 slot)

/-- The two exact lane-port endpoints let the radial and local pieces join
to an orthogonal complete route. -/
theorem retainedTerminalFanOuterCompleteRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterCompleteRoute
        center terminal slot) := by
  exact
    (retainedTerminalFanOuterRadialRoute_orthogonal
      center terminal slot).joinAtEndpoint
      (retainedTerminalFanOuterLocalRouteAt_orthogonal
        center terminal.1 slot)
      (retainedTerminalFanOuterRadialRoute_getLast?
        center terminal slot lengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot)

/-- Optional complete outer route selected by one length-aware profile
slot. -/
def RetainedAngularTerminalProfile.outerCompleteRoute
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    Option (List Cell) :=
  profile.terminals[slot.val]?.map fun terminal =>
    retainedTerminalFanOuterCompleteRoute
      center terminal slot

/-- An active profile slot selects its exact terminal-and-slot route. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoute_eq_some
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (terminal : RetainedTerminalData)
    (terminalLookup :
      profile.terminals[slot.val]? = some terminal) :
    profile.outerCompleteRoute center slot =
      some
        (retainedTerminalFanOuterCompleteRoute
          center terminal slot) := by
  simp [outerCompleteRoute, terminalLookup]

/-- An inactive profile slot selects no complete outer route. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoute_eq_none
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (terminalLookup :
      profile.terminals[slot.val]? = none) :
    profile.outerCompleteRoute center slot = none := by
  simp [outerCompleteRoute, terminalLookup]

/-- Every terminal selected by a profile has positive retained-ray
length. -/
theorem RetainedAngularTerminalProfile.length_positive_of_lookup
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot)
    (terminal : RetainedTerminalData)
    (terminalLookup :
      profile.terminals[slot.val]? = some terminal) :
    0 < terminal.2 := by
  rcases List.getElem?_eq_some_iff.mp terminalLookup with
    ⟨slotLt, terminalEq⟩
  rw [← terminalEq]
  exact profile.lengthsPositive
    profile.terminals[slot.val]
    (List.getElem_mem slotLt)

/-- Every complete route selected by a profile is orthogonal. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoute_orthogonal
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (terminal : RetainedTerminalData)
    (terminalLookup :
      profile.terminals[slot.val]? = some terminal) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterCompleteRoute
        center terminal slot) := by
  exact retainedTerminalFanOuterCompleteRoute_orthogonal
    center terminal slot
    (profile.length_positive_of_lookup
      slot terminal terminalLookup)

/-- Looking up a genuine occurrence selects its exact complete
source-gate-to-Figure-7 route. -/
theorem retainedAngularTerminalProfile_outerCompleteRoute_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom)
    (center : Cell) :
    let profile :=
      retainedAngularTerminalProfile
        source routes certificate fits atom
    let slot :=
      retainedAngularTerminalSlot
        source routes fits atom copy copyMember
    profile.outerCompleteRoute center slot =
      some
        (retainedTerminalFanOuterCompleteRoute center
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes copy))
          slot) := by
  dsimp only
  apply
    RetainedAngularTerminalProfile.outerCompleteRoute_eq_some
  exact
    retainedAngularTerminalProfile_getElem_slot
      source routes certificate fits atom copy copyMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes

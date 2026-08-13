/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterCompleteSeparation

/-!
# Finite retained outer fan route families

A length-aware terminal profile lists at most eight active source
incidences in angular order.  This file packages their complete
source-gate-to-Figure-7 routes as a list in exactly that order.  The
profile's positivity and duplicate-free-gate certificates then give every
listed route its exact endpoints and orthogonality, and make the whole
family pairwise strictly separated.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Convert an index into a profile's active terminal list to its
corresponding one-of-eight router slot. -/
def RetainedAngularTerminalProfile.terminalSlotOfIndex
    (profile : RetainedAngularTerminalProfile)
    (index : Fin profile.terminals.length) :
    RetainedTerminalSlot :=
  ⟨index.val, lt_of_lt_of_le index.isLt profile.fitsEight⟩

/-- Complete outer routes for all active terminals, in profile order. -/
def RetainedAngularTerminalProfile.outerCompleteRoutes
    (profile : RetainedAngularTerminalProfile)
    (center : Cell) : List (List Cell) :=
  List.ofFn fun index : Fin profile.terminals.length =>
    retainedTerminalFanOuterCompleteRoute center
      profile.terminals[index]
      (profile.terminalSlotOfIndex index)

@[simp]
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_length
    (profile : RetainedAngularTerminalProfile)
    (center : Cell) :
    (profile.outerCompleteRoutes center).length =
      profile.terminals.length := by
  simp [outerCompleteRoutes]

/-- A profile's complete outer-route family contains at most eight
routes. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_length_le_eight
    (profile : RetainedAngularTerminalProfile)
    (center : Cell) :
    (profile.outerCompleteRoutes center).length ≤ 8 := by
  rw [profile.outerCompleteRoutes_length]
  exact profile.fitsEight

@[simp]
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_getElem
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (index : Nat)
    (indexLt : index < profile.terminals.length) :
    (profile.outerCompleteRoutes center)[index]'(by simpa using indexLt) =
      retainedTerminalFanOuterCompleteRoute center
        profile.terminals[index]
        ⟨index, lt_of_lt_of_le indexLt profile.fitsEight⟩ := by
  simp [outerCompleteRoutes, terminalSlotOfIndex]

/-- Distinct retained source gates make the ordered finite family
pairwise strictly separated. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_pairwise
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (center : Cell) :
    (profile.outerCompleteRoutes center).Pairwise
      RoutesStrictlyAvoidEachOther := by
  rw [List.pairwise_iff_getElem]
  intro first second firstLt secondLt before
  have firstProfileLt : first < profile.terminals.length := by
    simpa using firstLt
  have secondProfileLt : second < profile.terminals.length := by
    simpa using secondLt
  rw [profile.outerCompleteRoutes_getElem
    center first firstProfileLt]
  rw [profile.outerCompleteRoutes_getElem
    center second secondProfileLt]
  apply profile.outerCompleteRoutes_strictlyAvoid
    distinct center
      ⟨first, lt_of_lt_of_le firstProfileLt profile.fitsEight⟩
      ⟨second, lt_of_lt_of_le secondProfileLt profile.fitsEight⟩
      profile.terminals[first] profile.terminals[second]
  · rw [List.getElem?_eq_getElem firstProfileLt]
  · rw [List.getElem?_eq_getElem secondProfileLt]
  · exact before

/-- Every member of the finite complete outer-route family is
orthogonal. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_orthogonal
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (route : List Cell)
    (routeMember : route ∈ profile.outerCompleteRoutes center) :
    PeriodicOrthocrossing.OrthogonalPolyline route := by
  rcases List.mem_iff_getElem.mp routeMember with
    ⟨index, indexLt, routeEq⟩
  have profileLt : index < profile.terminals.length := by
    simpa using indexLt
  rw [← routeEq,
    profile.outerCompleteRoutes_getElem center index profileLt]
  exact retainedTerminalFanOuterCompleteRoute_orthogonal
    center profile.terminals[index]
    ⟨index, lt_of_lt_of_le profileLt profile.fitsEight⟩
    (profile.lengthsPositive
      profile.terminals[index] (List.getElem_mem profileLt))

/-- Each indexed route has the exact source gate and refined Figure 7
boundary endpoint belonging to that profile slot, and is orthogonal. -/
theorem RetainedAngularTerminalProfile.outerCompleteRoutes_valid
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (index : Nat)
    (indexLt : index < profile.terminals.length) :
    let slot : RetainedTerminalSlot :=
      ⟨index, lt_of_lt_of_le indexLt profile.fitsEight⟩
    ((profile.outerCompleteRoutes center)[index]'(by
          simpa using indexLt)).head? =
        some
          (retainedAngularFanOuterDemand
            center profile.terminals[index] slot).gate ∧
      ((profile.outerCompleteRoutes center)[index]'(by
          simpa using indexLt)).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset index))) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        ((profile.outerCompleteRoutes center)[index]'(by
          simpa using indexLt)) := by
  dsimp only
  rw [profile.outerCompleteRoutes_getElem center index indexLt]
  have lengthPositive :=
    profile.lengthsPositive
      profile.terminals[index] (List.getElem_mem indexLt)
  exact ⟨retainedTerminalFanOuterCompleteRoute_head? _ _ _,
    by
      simpa using
        retainedTerminalFanOuterCompleteRoute_getLast?
          center profile.terminals[index]
          ⟨index, lt_of_lt_of_le indexLt profile.fitsEight⟩
          lengthPositive,
    retainedTerminalFanOuterCompleteRoute_orthogonal
      center profile.terminals[index]
      ⟨index, lt_of_lt_of_le indexLt profile.fitsEight⟩
      lengthPositive⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes

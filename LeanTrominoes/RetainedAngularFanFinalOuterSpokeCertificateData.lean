/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineStrictSeparationCheck
import LeanTrominoes.OrthogonalPolylineSegmentBoxCheck
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackBoundarySeparation
import LeanTrominoes.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterCycleSeparation

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A Figure 7 spoke recentered at the old variable position and refined
to the common terminal-fan grid. -/
def retainedTerminalFanCenteredFigure7Spoke
    (slot : RetainedTerminalSlot) : List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    ((spokeRoute (angularPortOfIndex slot.val)).map
      (Cell.add (-12, -12)))

/-- Translating the centered spoke gives the positioned Figure 7 spoke
used by the final fallback construction. -/
theorem retainedTerminalFanCenteredFigure7Spoke_map_add
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanCenteredFigure7Spoke slot).map
        (Cell.add center) =
      retainedTerminalFanFigure7SpokeRouteAt center slot := by
  unfold retainedTerminalFanCenteredFigure7Spoke
    retainedTerminalFanFigure7SpokeRouteAt
    PeriodicOrthocrossing.translatePolyline scalePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

def outerCenteredPairCheck (first second : List Cell) : Bool :=
  segmentBoxesSeparateCheck first second || routesStrictlyAvoidEachOtherCheck first second

theorem outerCenteredPairCheck_sound (first second : List Cell)
    (checked : outerCenteredPairCheck first second = true) : RoutesStrictlyAvoidEachOther first second := by
  simp only [outerCenteredPairCheck, Bool.or_eq_true] at checked
  rcases checked with boxes | exactCheck
  · exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck first second boxes
  · exact (routesStrictlyAvoidEachOtherCheck_eq_true first second).mp exactCheck

def outerCenteredLocalCheck (direction : RetainedTerminalDirection) : Bool :=
  finiteAll fun firstSlot : RetainedTerminalSlot =>
    finiteAll fun secondSlot : RetainedTerminalSlot =>
      guardedCheck (firstSlot ≠ secondSlot)
        (outerCenteredPairCheck (retainedTerminalFanOuterLocalRoute direction firstSlot)
          (retainedTerminalFanCenteredFigure7Spoke secondSlot))

def outerCenteredStubCheck (direction : RetainedTerminalDirection) : Bool :=
  finiteAll fun firstSlot : RetainedTerminalSlot =>
    finiteAll fun secondSlot : RetainedTerminalSlot =>
      outerCenteredPairCheck (retainedTerminalFanOuterRadialFinalStub direction firstSlot)
        (retainedTerminalFanCenteredFigure7Spoke secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

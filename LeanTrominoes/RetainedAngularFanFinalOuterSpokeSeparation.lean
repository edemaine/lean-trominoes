import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackBoundarySeparation
import LeanTrominoes.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterCycleSeparation

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private theorem map_add_zero (route : List Cell) :
    route.map (Cell.add (0, 0)) = route := by
  induction route with
  | nil => rfl
  | cons point points induction =>
      simp [induction, Cell.add]

/-- A Figure 7 spoke recentered at the old variable position and refined
to the common terminal-fan grid. -/
def retainedTerminalFanCenteredFigure7Spoke
    (slot : RetainedTerminalSlot) : List Cell :=
  scalePolyline retainedTerminalFanRoutingRefinement
    ((spokeRoute (angularPortOfIndex slot.val)).map
      (Cell.add (-12, -12)))

/-- A complete ordinary outer-fan route is contact-free from every
different Figure 7 spoke in the same variable macrocell. -/
theorem
    retainedTerminalFanOuterLocalRoute_strictlyAvoid_otherCenteredFigure7Spoke :
    ∀ (direction : RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstSlot ≠ secondSlot →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterLocalRoute
            direction firstSlot)
          (retainedTerminalFanCenteredFigure7Spoke
            secondSlot) := by
  native_decide

/-- Every centered refined Figure 7 spoke stays in the radius-96 square. -/
theorem retainedTerminalFanCenteredFigure7Spoke_points_within :
    ∀ (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanCenteredFigure7Spoke slot →
        WithinCoordinateRadius 96 (0, 0) point := by
  native_decide

/-- A centered Figure 7 spoke lies below the supporting line selected by
every retained terminal direction. -/
theorem retainedTerminalFanCenteredFigure7Spoke_side_upper
    (sideDirection : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanCenteredFigure7Spoke slot) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal sideDirection)
        point ≤ 96 := by
  have bounded :=
    retainedTerminalFanCenteredFigure7Spoke_points_within
      slot point pointMember
  have coordinateBounds := bounded.coordinate_bounds
  rcases sideDirection with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterSideNormal,
      Cell.linearValue] at coordinateBounds ⊢ <;>
    omega

/-- Every final radial stub is separated from every centered Figure 7
spoke. -/
theorem
    retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_centeredFigure7Spoke :
    ∀ (direction : RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterRadialFinalStub
          direction firstSlot)
        (retainedTerminalFanCenteredFigure7Spoke
          secondSlot) := by
  native_decide

/-- The arbitrary-length exterior part of an ordinary radial route avoids
every centered Figure 7 spoke. -/
theorem
    retainedTerminalFanOuterRadialPrefix_strictlyAvoid_centeredFigure7Spoke
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialPrefix
        (0, 0) terminal firstSlot)
      (retainedTerminalFanCenteredFigure7Spoke
        secondSlot) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      288
      (fun point pointMember => by
        have inner :=
          retainedTerminalFanCenteredFigure7Spoke_side_upper
            terminal.1 secondSlot point pointMember
        omega)
      (by
        simpa [Cell.linearValue] using
          retainedTerminalFanOuterRadialPrefix_side_lower
            (0, 0) terminal firstSlot
            radialLengthPositive)).symm

/-- The explicit split ordinary radial route avoids every centered Figure
7 spoke. -/
theorem splitRadialRoute_strictlyAvoid_centeredFigure7Spoke
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (splitRadialRoute (0, 0) terminal firstSlot)
      (retainedTerminalFanCenteredFigure7Spoke
        secondSlot) := by
  unfold splitRadialRoute
  exact
    (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_centeredFigure7Spoke
      terminal firstSlot secondSlot radialLengthPositive).join_left
      (by
        simpa [retainedTerminalFanOuterRadialFinalStubAt,
          map_add_zero] using
          retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_centeredFigure7Spoke
            terminal.1 firstSlot secondSlot)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        (0, 0) terminal firstSlot radialLengthPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        (0, 0) terminal.1 firstSlot)

/-- Every positive ordinary radial route avoids every centered Figure 7
spoke; the direct cardinal route follows by certified middle coarsening. -/
theorem
    retainedTerminalFanOuterRadialRoute_strictlyAvoid_centeredFigure7Spoke
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        (0, 0) terminal firstSlot)
      (retainedTerminalFanCenteredFigure7Spoke
        secondSlot) := by
  have splitAvoid :=
    splitRadialRoute_strictlyAvoid_centeredFigure7Spoke
      terminal firstSlot secondSlot radialLengthPositive
  by_cases blocked : terminal.1.usesBlockedRaster
  · rw [radialRoute_eq_split_of_usesBlockedRaster
      (0, 0) terminal firstSlot radialLengthPositive blocked]
    exact splitAvoid
  · rcases radialRoute_direct_coarsening
      (0, 0) terminal firstSlot radialLengthPositive blocked with
      ⟨leading, first, middle, finish,
        splitEq, radialEq, leadingLast, middleInterior⟩
    rw [splitEq] at splitAvoid
    rw [radialEq]
    exact splitAvoid.coarsen_middle_after_join_left
      leadingLast middleInterior

/-- A complete ordinary outer-fan route avoids every different centered
Figure 7 spoke. -/
theorem
    retainedTerminalFanOuterCompleteRoute_strictlyAvoid_otherCenteredFigure7Spoke
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        (0, 0) terminal firstSlot)
      (retainedTerminalFanCenteredFigure7Spoke
        secondSlot) := by
  unfold retainedTerminalFanOuterCompleteRoute
  exact
    (retainedTerminalFanOuterRadialRoute_strictlyAvoid_centeredFigure7Spoke
      terminal firstSlot secondSlot radialLengthPositive).join_left
      (by
        simpa [retainedTerminalFanOuterLocalRouteAt,
          map_add_zero] using
          retainedTerminalFanOuterLocalRoute_strictlyAvoid_otherCenteredFigure7Spoke
            terminal.1 firstSlot secondSlot slotsDifferent)
      (retainedTerminalFanOuterRadialRoute_getLast?
        (0, 0) terminal firstSlot lengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        (0, 0) terminal.1 firstSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

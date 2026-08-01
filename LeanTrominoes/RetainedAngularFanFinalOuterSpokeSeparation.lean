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

/-- A positioned ordinary radial prefix avoids every positioned Figure 7
spoke at the same macrocell center. -/
theorem
    retainedTerminalFanOuterRadialPrefix_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialPrefix
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  apply
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        center + 288)
      (fun point pointMember => by
        rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
          at pointMember
        rcases List.mem_map.mp pointMember with
          ⟨offset, offsetMember, rfl⟩
        have upper :=
          retainedTerminalFanCenteredFigure7Spoke_side_upper
            terminal.1 secondSlot offset offsetMember
        have linearAdd :
            Cell.linearValue
                (retainedTerminalFanOuterSideNormal terminal.1)
                (Cell.add center offset) =
              Cell.linearValue
                  (retainedTerminalFanOuterSideNormal terminal.1)
                  center +
                Cell.linearValue
                  (retainedTerminalFanOuterSideNormal terminal.1)
                  offset := by
          simp [Cell.linearValue, Cell.add]
          ring
        rw [linearAdd]
        omega)
      (retainedTerminalFanOuterRadialPrefix_side_lower
        center terminal firstSlot radialLengthPositive)).symm

/-- A positioned final radial stub avoids every positioned Figure 7 spoke
at the same macrocell center. -/
theorem
    retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialFinalStubAt
        center direction firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  have translated :=
    (retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_centeredFigure7Spoke
      direction firstSlot secondSlot).map_add center
  rw [show
      (retainedTerminalFanOuterRadialFinalStub
        direction firstSlot).map (Cell.add center) =
          retainedTerminalFanOuterRadialFinalStubAt
            center direction firstSlot by rfl,
    retainedTerminalFanCenteredFigure7Spoke_map_add] at translated
  exact translated

/-- The explicitly split positioned radial route avoids every positioned
Figure 7 spoke at the same center. -/
theorem splitRadialRoute_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (splitRadialRoute center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  unfold splitRadialRoute
  exact
    (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_figure7SpokeRouteAt
      center terminal firstSlot secondSlot
      radialLengthPositive).join_left
      (retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_figure7SpokeRouteAt
        center terminal.1 firstSlot secondSlot)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center terminal firstSlot radialLengthPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center terminal.1 firstSlot)

/-- Every positive positioned ordinary radial route avoids every
positioned Figure 7 spoke at the same center. -/
theorem
    retainedTerminalFanOuterRadialRoute_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  have splitAvoid :=
    splitRadialRoute_strictlyAvoid_figure7SpokeRouteAt
      center terminal firstSlot secondSlot radialLengthPositive
  by_cases blocked : terminal.1.usesBlockedRaster
  · rw [radialRoute_eq_split_of_usesBlockedRaster
      center terminal firstSlot radialLengthPositive blocked]
    exact splitAvoid
  · rcases radialRoute_direct_coarsening
      center terminal firstSlot radialLengthPositive blocked with
      ⟨leading, first, middle, finish,
        splitEq, radialEq, leadingLast, middleInterior⟩
    rw [splitEq] at splitAvoid
    rw [radialEq]
    exact splitAvoid.coarsen_middle_after_join_left
      leadingLast middleInterior

/-- A positioned local outer-fan route avoids every different positioned
Figure 7 spoke at the same center. -/
theorem
    retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_otherFigure7SpokeRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center direction firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  have translated :=
    (retainedTerminalFanOuterLocalRoute_strictlyAvoid_otherCenteredFigure7Spoke
      direction firstSlot secondSlot slotsDifferent).map_add center
  rw [show
      (retainedTerminalFanOuterLocalRoute
        direction firstSlot).map (Cell.add center) =
          retainedTerminalFanOuterLocalRouteAt
            center direction firstSlot by rfl,
    retainedTerminalFanCenteredFigure7Spoke_map_add] at translated
  exact translated

/-- A complete positioned ordinary outer-fan route avoids every different
positioned Figure 7 spoke at the same center. -/
theorem
    retainedTerminalFanOuterCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  unfold retainedTerminalFanOuterCompleteRoute
  exact
    (retainedTerminalFanOuterRadialRoute_strictlyAvoid_figure7SpokeRouteAt
      center terminal firstSlot secondSlot
      radialLengthPositive).join_left
      (retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_otherFigure7SpokeRouteAt
        center terminal.1 firstSlot secondSlot slotsDifferent)
      (retainedTerminalFanOuterRadialRoute_getLast?
        center terminal firstSlot lengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 firstSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

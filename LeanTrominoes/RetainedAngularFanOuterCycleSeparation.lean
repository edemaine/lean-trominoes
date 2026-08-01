import LeanTrominoes.OccurrenceSplitRingSpokeCycleSeparation
import LeanTrominoes.RetainedAngularFanOuterCrossSeparation

/-!
# Separating ordinary outer fan routes from the inner implication cycle

Every factor-eight implication route lies in the radius-48 square around
its retained variable center.  The finite outer fan adapter and final radial
stub are certified directly against that square.  The arbitrary-length
radial prefix lies beyond the radius-288 supporting side, so a linear
separator handles it without depending on the source-route length.

Together these facts prove that every positive ordinary outer fan route is
strictly contact-free from every implication route in its own Figure 7
cycle.  This is the replacement-fan half of matching-cycle separation for
ordinary copied-source fallback routes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- One factor-eight implication route centered at the retained source
variable position. -/
def retainedTerminalFanInnerCycleRoute
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    List Cell :=
  translatePolyline
    (Cell.sub (0, 0)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline retainedTerminalFanRoutingRefinement
      (cycleRoute vertex literalIndex.val))

/-- Every listed point of a centered factor-eight implication route lies
in the radius-48 inner square. -/
theorem retainedTerminalFanInnerCycleRoute_points_within_inner_square :
    ∀ (vertex : RingVertex)
      (literalIndex : Fin 2)
      (point : Cell),
      point ∈ retainedTerminalFanInnerCycleRoute vertex literalIndex →
        WithinCoordinateRadius 48 (0, 0) point := by
  intro vertex
  cases vertex with
  | separator => native_decide
  | port port =>
      cases port <;> native_decide

/-- Translate a centered implication route to an arbitrary retained source
variable position. -/
def retainedTerminalFanInnerCycleRouteAt
    (center : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    List Cell :=
  translatePolyline center
    (retainedTerminalFanInnerCycleRoute vertex literalIndex)

/-- A positioned inner implication route lies below the radius-48 supporting
line selected by any retained terminal direction. -/
theorem retainedTerminalFanInnerCycleRouteAt_side_upper
    (center : Cell)
    (sideDirection : RetainedTerminalDirection)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal sideDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal sideDirection)
          center +
        48 := by
  unfold retainedTerminalFanInnerCycleRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  have bounded :=
    retainedTerminalFanInnerCycleRoute_points_within_inner_square
      vertex literalIndex offset offsetMember
  have coordinateBounds := bounded.coordinate_bounds
  rcases sideDirection with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterSideNormal,
      Cell.linearValue, Cell.add] at coordinateBounds ⊢ <;>
    omega

/-- Every finite radius-288-to-Figure-7 adapter strictly avoids every
centered inner implication route. -/
theorem retainedTerminalFanOuterLocalRoute_strictlyAvoid_innerCycleRoute :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot)
      (vertex : RingVertex)
      (literalIndex : Fin 2),
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterLocalRoute direction slot)
        (retainedTerminalFanInnerCycleRoute vertex literalIndex) := by
  intro direction slot vertex literalIndex
  cases vertex with
  | separator =>
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        revert slot literalIndex <;>
        native_decide
  | port port =>
      cases port <;>
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          revert slot literalIndex <;>
          native_decide

/-- Positioning both the finite adapter and inner cycle preserves their
strict separation. -/
theorem retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center direction slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterLocalRoute_strictlyAvoid_innerCycleRoute
      direction slot vertex literalIndex)
    center

/-- Every final radial primitive stub strictly avoids every centered inner
implication route. -/
theorem
    retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_innerCycleRoute :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot)
      (vertex : RingVertex)
      (literalIndex : Fin 2),
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterRadialFinalStub direction slot)
        (retainedTerminalFanInnerCycleRoute vertex literalIndex) := by
  intro direction slot vertex literalIndex
  cases vertex with
  | separator =>
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        revert slot literalIndex <;>
        native_decide
  | port port =>
      cases port <;>
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          revert slot literalIndex <;>
          native_decide

/-- Positioning both a final radial stub and inner cycle preserves their
strict separation. -/
theorem
    retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialFinalStubAt
        center direction slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_innerCycleRoute
      direction slot vertex literalIndex)
    center

/-- The strictly exterior radial prefix avoids every positioned inner
implication route by the radius-288 supporting line. -/
theorem
    retainedTerminalFanOuterRadialPrefix_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialPrefix
        center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 288)
      (fun point pointMember => by
        have inner :=
          retainedTerminalFanInnerCycleRouteAt_side_upper
            center terminal.1 vertex literalIndex
            point pointMember
        omega)
      (retainedTerminalFanOuterRadialPrefix_side_lower
        center terminal slot radialLengthPositive)).symm

/-- The explicit prefix/final-stub decomposition of a positive radial route
strictly avoids every positioned inner implication route. -/
theorem splitRadialRoute_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (splitRadialRoute center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  unfold splitRadialRoute
  exact
    (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_innerCycleRouteAt
      center terminal slot vertex literalIndex
      radialLengthPositive).join_left
      (retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_innerCycleRouteAt
        center terminal.1 slot vertex literalIndex)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center terminal slot radialLengthPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center terminal.1 slot)

/-- Every positive ordinary radial route strictly avoids every positioned
inner implication route.  Cardinal route coarsening preserves the
continuous certificate. -/
theorem
    retainedTerminalFanOuterRadialRoute_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  have splitAvoid :=
    splitRadialRoute_strictlyAvoid_innerCycleRouteAt
      center terminal slot vertex literalIndex
      radialLengthPositive
  by_cases blocked : terminal.1.usesBlockedRaster
  · rw [radialRoute_eq_split_of_usesBlockedRaster
      center terminal slot radialLengthPositive blocked]
    exact splitAvoid
  · rcases radialRoute_direct_coarsening
      center terminal slot radialLengthPositive blocked with
      ⟨leading, first, middle, finish,
        splitEq, radialEq, leadingLast, middleInterior⟩
    rw [splitEq] at splitAvoid
    rw [radialEq]
    exact splitAvoid.coarsen_middle_after_join_left
      leadingLast middleInterior

/-- A positive complete ordinary source-to-Figure-7 fan route strictly
avoids every implication route in its own inner cycle. -/
theorem
    retainedTerminalFanOuterCompleteRoute_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (lengthPositive : 0 < terminal.2)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  unfold retainedTerminalFanOuterCompleteRoute
  exact
    (retainedTerminalFanOuterRadialRoute_strictlyAvoid_innerCycleRouteAt
      center terminal slot vertex literalIndex
      radialLengthPositive).join_left
      (retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_innerCycleRouteAt
        center terminal.1 slot vertex literalIndex)
      (retainedTerminalFanOuterRadialRoute_getLast?
        center terminal slot lengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

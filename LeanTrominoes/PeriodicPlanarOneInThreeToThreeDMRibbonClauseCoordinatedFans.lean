import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseLocalGates

/-!
# Complete coordinated clause-side ribbon fans

This file joins each reflected clause outer-fan route to its corresponding
local gate-to-port route.  The resulting physical strand begins at the
direction-dependent ribbon entry and ends at the exact lane assigned to its
clause-core terminal.

Finite checking establishes the interface between the two route tables:
matching pieces meet only at their advertised gate, while pieces belonging
to distinct strands are strictly separated.  The complete routes are then
certified to be simple, rectilinear, bounded, mutually separated, and
disjoint from the clause core except at their advertised terminal ports.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-! ## Finite interface between the two route tables -/

/-- Every selected outer route avoids every selected local route.  For the
matching pair, their advertised common gate is the only possible contact. -/
theorem clauseOuterRoute_avoids_localGateRoute :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ outerGroup localGroup,
        data.GroupActive outerGroup →
        data.GroupActive localGroup →
        ∀ outerLane localLane,
          RoutesAvoidEachOther
            (data.outerRoute outerGroup outerLane)
            (data.localGateRoute localGroup localLane) := by
  native_decide

/-- Outer and local table pieces belonging to distinct physical strands
have no contact at all. -/
theorem clauseOuterRoute_strictlyAvoids_localGateRoute :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ outerGroup localGroup,
        data.GroupActive outerGroup →
        data.GroupActive localGroup →
        ∀ outerLane localLane,
          (outerGroup, outerLane) ≠ (localGroup, localLane) →
          RoutesStrictlyAvoidEachOther
            (data.outerRoute outerGroup outerLane)
            (data.localGateRoute localGroup localLane) := by
  native_decide

/-- Each complete finite outer-plus-local clause route is geometrically
simple. -/
theorem joinedClauseOuterGateRoute_simple :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
        ∀ lane,
          LocalIncidenceDrawing.RouteIsSimple
            (joinAtEndpoint
              (data.outerRoute group lane)
              (data.localGateRoute group lane)) := by
  native_decide

namespace ClauseRibbonFanData

/-- Complete standard-macrocell clause route from a physical ribbon entry
to the corresponding exact clause-core port. -/
def coordinatedRoute
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : List Cell :=
  joinAtEndpoint
    (data.outerRoute group lane)
    (data.localGateRoute group lane)

/-- A coordinated clause route starts at its direction-dependent ribbon
entry. -/
@[simp]
theorem coordinatedRoute_head?
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor) :
    (data.coordinatedRoute group lane).head? =
      some (standardRibbonMacrocellEntry
        (data.direction group) lane) := by
  apply joinAtEndpoint_head?
  exact data.outerRoute_head? compatible group active lane

/-- A coordinated clause route ends at its exact physical-lane core port. -/
@[simp]
theorem coordinatedRoute_getLast?
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor) :
    (data.coordinatedRoute group lane).getLast? =
      some (lanePort group lane) := by
  apply joinAtEndpoint_getLast?
  · exact data.outerRoute_getLast? compatible group active lane
  · exact data.localGateRoute_head? group active lane
  · exact data.localGateRoute_getLast? group active lane

/-- Every complete coordinated clause route is rectilinear. -/
theorem coordinatedRoute_orthogonal
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor) :
    OrthogonalPolyline (data.coordinatedRoute group lane) := by
  apply
    (data.outerRoute_orthogonal compatible group active lane).joinAtEndpoint
  · exact data.localGateRoute_orthogonal group active lane
  · exact data.outerRoute_getLast? compatible group active lane
  · exact data.localGateRoute_head? group active lane

/-- Every point of a coordinated clause route stays in the standard ribbon
macrocell. -/
theorem coordinatedRoute_points_bounded
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor)
    {point : Cell}
    (member : point ∈ data.coordinatedRoute group lane) :
    InStandardRibbonMacrocell point := by
  rcases mem_joinAtEndpoint member with outerMember | localMember
  · exact data.outerRoute_points_bounded
      compatible group active lane point outerMember
  · exact data.localGateRoute_points_bounded
      group active lane point localMember

/-- Each complete coordinated clause route is geometrically simple. -/
theorem coordinatedRoute_simple
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (data.coordinatedRoute group lane) := by
  exact joinedClauseOuterGateRoute_simple
    data compatible group active lane

/-- A complete coordinated clause route meets the finite clause-core
drawing only at advertised common route endpoints. -/
theorem coordinatedRoute_avoids_clauseCore
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor)
    (set : X3CClauseSet)
    (color : WireColor) :
    RoutesAvoidEachOther
      (data.coordinatedRoute group lane)
      (translatePolyline standardThreeStrandLayout.clauseOffset
        (X3CClauseOrthogonal.route set color)) := by
  native_decide +revert

/-- Distinct active physical strands in a complete coordinated clause fan
have no continuous or listed-point contact. -/
theorem coordinatedRoutes_strictlyAvoidEachOther
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (firstGroup secondGroup : X3CClauseTerminalGroup)
    (firstActive : data.GroupActive firstGroup)
    (secondActive : data.GroupActive secondGroup)
    (firstLane secondLane : WireColor)
    (different :
      (firstGroup, firstLane) ≠ (secondGroup, secondLane)) :
    RoutesStrictlyAvoidEachOther
      (data.coordinatedRoute firstGroup firstLane)
      (data.coordinatedRoute secondGroup secondLane) := by
  native_decide +revert

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

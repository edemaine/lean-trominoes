import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseOuterFans

/-!
# Clause-side local ribbon gates

The reflected outer fans end at fixed physical-lane gates.  This file
connects those gates to the exact top, left, and optional right clause-core
ports.  The two- and three-terminal cases use separate simultaneous routing
tables because their reflected gates occupy different horizontal clusters.

Every table stays inside the protected central rectangle left unused by all
outer-fan templates.  It also stays outside the complete clause-core drawing
except at its advertised terminal endpoint.  All endpoint, rectilinearity,
simplicity, containment, core-avoidance, and pairwise-separation claims are
checked exhaustively by Lean.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

namespace ClauseRibbonFanData

/-- Simultaneous gate-to-port route for one physical clause strand. -/
def localGateRoute
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : List Cell :=
  match data.hasRight, group, lane with
  | false, .top, .red =>
      [(76, 108), (76, 103), (75, 103), (75, 95),
        (74, 95), (74, 91), (73, 91), (73, 88),
        (67, 88), (67, 87), (59, 87), (59, 86),
        (53, 86), (53, 85), (45, 85), (45, 59),
        (54, 59), (54, 60)]
  | false, .top, .green =>
      [(72, 108), (72, 90), (71, 90), (71, 89),
        (66, 89), (66, 88), (58, 88), (58, 87),
        (52, 87), (52, 86), (44, 86), (44, 58),
        (62, 58), (62, 60)]
  | false, .top, .blue =>
      [(68, 108), (68, 103), (67, 103), (67, 100),
        (65, 100), (65, 97), (64, 97), (64, 89),
        (57, 89), (57, 88), (51, 88), (51, 87),
        (43, 87), (43, 57), (68, 57), (68, 58),
        (70, 58), (70, 60)]
  | false, .left, .red =>
      [(108, 108), (108, 99), (107, 99), (107, 96),
        (106, 96), (106, 95), (105, 95), (105, 93),
        (104, 93), (104, 86), (103, 86), (103, 85),
        (70, 85), (70, 84)]
  | false, .left, .green =>
      [(104, 108), (104, 106), (103, 106), (103, 87),
        (102, 87), (102, 86), (69, 86), (69, 85),
        (62, 85), (62, 84)]
  | false, .left, .blue =>
      [(100, 108), (100, 107), (99, 107), (99, 105),
        (98, 105), (98, 96), (97, 96), (97, 93),
        (95, 93), (95, 90), (94, 90), (94, 87),
        (68, 87), (68, 86), (61, 86), (61, 85),
        (54, 85), (54, 84)]
  | false, .right, _ => []
  | true, .top, .red =>
      [(44, 108), (44, 57), (54, 57), (54, 60)]
  | true, .top, .green =>
      [(40, 108), (40, 54), (62, 54), (62, 60)]
  | true, .top, .blue =>
      [(36, 108), (36, 51), (70, 51), (70, 60)]
  | true, .left, .red =>
      [(76, 108), (76, 88), (70, 88), (70, 84)]
  | true, .left, .green =>
      [(72, 108), (72, 90), (62, 90), (62, 84)]
  | true, .left, .blue =>
      [(68, 108), (68, 92), (54, 92), (54, 84)]
  | true, .right, .red =>
      [(108, 108), (108, 64), (78, 64)]
  | true, .right, .green =>
      [(104, 108), (104, 72), (78, 72)]
  | true, .right, .blue =>
      [(100, 108), (100, 80), (78, 80)]

/-- Every active local route starts at its reflected physical-lane gate. -/
@[simp]
theorem localGateRoute_head? :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane,
        (data.localGateRoute group lane).head? =
          some (data.outerGate group lane) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Every active local route ends at its exact physical-lane clause port. -/
@[simp]
theorem localGateRoute_getLast? :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane,
        (data.localGateRoute group lane).getLast? =
          some (lanePort group lane) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Every active local gate route is rectilinear. -/
theorem localGateRoute_orthogonal :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane, OrthogonalPolyline (data.localGateRoute group lane) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Every active local gate route is geometrically simple. -/
theorem localGateRoute_simple :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane,
        LocalIncidenceDrawing.RouteIsSimple
          (data.localGateRoute group lane) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Every local gate-route point remains in the standard ribbon macrocell. -/
theorem localGateRoute_points_bounded :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane point,
        point ∈ data.localGateRoute group lane →
        InStandardRibbonMacrocell point := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Local clause routes meet the finite clause-core drawing only at
advertised common route endpoints. -/
theorem localGateRoute_avoids_clauseCore :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      ∀ lane set color,
        RoutesAvoidEachOther
          (data.localGateRoute group lane)
          (translatePolyline standardThreeStrandLayout.clauseOffset
            (X3CClauseOrthogonal.route set color)) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

/-- Distinct active local clause strands are strictly separated. -/
theorem localGateRoutes_strictlyAvoidEachOther :
    ∀ (data : ClauseRibbonFanData)
      firstGroup secondGroup,
      data.GroupActive firstGroup →
      data.GroupActive secondGroup →
      ∀ firstLane secondLane,
        (firstGroup, firstLane) ≠ (secondGroup, secondLane) →
        RoutesStrictlyAvoidEachOther
          (data.localGateRoute firstGroup firstLane)
          (data.localGateRoute secondGroup secondLane) := by
  rintro ⟨hasRight, direction⟩
  cases hasRight <;> native_decide +revert

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

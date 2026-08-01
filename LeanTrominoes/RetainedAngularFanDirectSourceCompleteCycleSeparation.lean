import LeanTrominoes.RetainedAngularFanDirectSourceCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Complete direct-source routes avoid their own implication cycle

A successful direct-source route is the endpoint join of its coordinated
outer prefix and one retained Figure 7 spoke.  The atlas certifies strict
prefix/cycle separation.  The finite Figure 7 drawing certifies ordinary
spoke/cycle separation, with every possible contact at the spoke's terminal
ring vertex.  The tail-contact join theorem therefore assembles the complete
mixed certificate.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The selected inner Figure 7 implication route in a direct choice's
physical component coordinates. -/
def RetainedDirectSourceRouteChoice.innerCycleRoute
    (choice : RetainedDirectSourceRouteChoice)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    List Cell :=
  translatePolyline
    (retainedDirectSourceFanPositioningOffset choice.origin)
    (retainedDirectSourceInnerCycleRouteAt
      choice.kind choice.index vertex literalIndex)

/-- The complete atlas prefix retains its strict inner-cycle certificate
after positioning at the selected component origin. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_innerCycle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute slot)
      (choice.innerCycleRoute vertex literalIndex) := by
  simpa [RetainedDirectSourceRouteChoice.innerCycleRoute] using
    choice.completeRoute_strictlyAvoids_innerCycleRoute
      slot vertex literalIndex

/-- The selected Figure 7 spoke ordinarily avoids every route in its own
inner implication cycle. -/
theorem RetainedDirectSourceRouteChoice.figure7Spoke_avoids_innerCycle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesAvoidEachOther
      (choice.figure7Spoke slot)
      (choice.innerCycleRoute vertex literalIndex) := by
  let localOffset :=
    Cell.sub
      (retainedDirectSourceFanCenterAt
        choice.kind choice.index)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (12, 12))
  have scaledAvoid :=
    (spokeRoute_avoids_cycleRoute
      (angularPortOfIndex slot.val)
      vertex literalIndex.val).scalePolyline
        (show
          (0 : Int) < retainedTerminalFanRoutingRefinement by
          simp [retainedTerminalFanRoutingRefinement])
  have localAvoid :=
    routesAvoidEachOther_translate
      scaledAvoid localOffset
  have positionedAvoid :=
    routesAvoidEachOther_translate
      localAvoid
      (retainedDirectSourceFanPositioningOffset
        choice.origin)
  simpa [RetainedDirectSourceRouteChoice.figure7Spoke,
    RetainedDirectSourceRouteChoice.innerCycleRoute,
    retainedDirectSourceFigure7SpokeAt,
    retainedDirectSourceInnerCycleRouteAt,
    PeriodicOrthocrossing.translatePolyline,
    List.map_map, localOffset] using positionedAvoid

/-- Every listed spoke/cycle contact remains at the spoke's final ring
vertex after both local and component positioning. -/
theorem
    RetainedDirectSourceRouteChoice.figure7Spoke_meets_innerCycle_only_at_tail
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesMeetOnlyAtFirstTail
      (choice.figure7Spoke slot)
      (choice.innerCycleRoute vertex literalIndex) := by
  let localOffset :=
    Cell.sub
      (retainedDirectSourceFanCenterAt
        choice.kind choice.index)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (12, 12))
  have scaledContacts :=
    (spokeRoute_meets_cycleRoute_only_at_tail
      (angularPortOfIndex slot.val)
      vertex literalIndex.val).scalePolyline
        (show
          (0 : Int) < retainedTerminalFanRoutingRefinement by
          simp [retainedTerminalFanRoutingRefinement])
  have localContacts :=
    scaledContacts.translate localOffset
  have positionedContacts :=
    localContacts.translate
      (retainedDirectSourceFanPositioningOffset
        choice.origin)
  simpa [RetainedDirectSourceRouteChoice.figure7Spoke,
    RetainedDirectSourceRouteChoice.innerCycleRoute,
    retainedDirectSourceFigure7SpokeAt,
    retainedDirectSourceInnerCycleRouteAt,
    PeriodicOrthocrossing.translatePolyline,
    List.map_map, localOffset] using positionedContacts

/-- The explicit complete direct occurrence assembled from an atlas prefix
and its selected Figure 7 spoke. -/
def RetainedDirectSourceRouteChoice.completeFigure7Route
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    List Cell :=
  joinAtEndpoint
    (choice.completeRoute slot)
    (choice.figure7Spoke slot)

/-- A complete positioned direct-source occurrence continuously avoids
every route in its own Figure 7 implication cycle.  The only permitted
listed contact is the occurrence route's final ring vertex. -/
theorem
    RetainedDirectSourceRouteChoice.completeFigure7Route_avoids_innerCycle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesAvoidEachOther
      (choice.completeFigure7Route slot)
      (choice.innerCycleRoute vertex literalIndex) := by
  let boundary :=
    Cell.add
      (retainedDirectSourceFanPositioningOffset choice.origin)
      (Cell.add
        (retainedDirectSourceFanCenterAt
          choice.kind choice.index)
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanBoundaryOffset slot.val)))
  have prefixLast :
      (choice.completeRoute slot).getLast? =
        some boundary := by
    simpa [boundary] using choice.completeRoute_getLast? slot
  have spokeHead :
      (choice.figure7Spoke slot).head? =
        some boundary := by
    rw [choice.figure7Spoke_head?, prefixLast]
  exact
    RoutesAvoidEachOther.join_left_of_tail_contact
      (choice.completeRoute_strictlyAvoids_innerCycle
        slot vertex literalIndex)
      (choice.figure7Spoke_avoids_innerCycle
        slot vertex literalIndex)
      (choice.figure7Spoke_meets_innerCycle_only_at_tail
        slot vertex literalIndex)
      prefixLast spokeHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes

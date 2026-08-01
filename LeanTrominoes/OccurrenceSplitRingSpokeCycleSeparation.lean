import LeanTrominoes.OccurrenceSplitRingDrawing
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Separation between Figure 7 spokes and implication routes

The complete finite Figure 7 drawing certifies not only its implication
cycle but also the eight old-incidence spokes entering that cycle.  This
module exposes the mixed spoke/cycle consequence directly and transports it
through the common scaling and translation used by the retained angular
construction.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every local old-incidence spoke and every local implication route satisfy
the complete continuous two-route separation predicate. -/
theorem spokeRoute_avoids_cycleRoute
    (port : Port)
    (vertex : RingVertex)
    (literalIndex : Nat) :
    RoutesAvoidEachOther
      (spokeRoute port)
      (cycleRoute vertex literalIndex) := by
  rcases literalIndex with _ | literalIndex
  · cases port <;>
      cases vertex with
      | separator => native_decide
      | port cyclePort =>
          cases cyclePort <;> native_decide
  · rcases literalIndex with _ | literalIndex
    · cases port <;>
        cases vertex with
        | separator => native_decide
        | port cyclePort =>
            cases cyclePort <;> native_decide
    · change RoutesAvoidEachOther (spokeRoute port) []
      simp [RoutesAvoidEachOther,
        SegmentInteriorsDisjoint, RoutePointsAvoidInteriors,
        RoutesMeetOnlyAtEndpoints, gridPolylineSegments]

/-- A local old-incidence spoke avoids the total presentation-indexed cycle
route lookup, including its empty out-of-range branch. -/
theorem spokeRoute_avoids_cycleRoutes
    (port : Port)
    (clauseIndex literalIndex : Nat) :
    RoutesAvoidEachOther
      (spokeRoute port)
      (cycleRoutes clauseIndex literalIndex) := by
  unfold cycleRoutes
  split
  · exact
      spokeRoute_avoids_cycleRoute
        port
        (presentedCycleVertices.getD
          clauseIndex .separator)
        literalIndex
  · simp [RoutesAvoidEachOther,
      SegmentInteriorsDisjoint, RoutePointsAvoidInteriors,
      RoutesMeetOnlyAtEndpoints, gridPolylineSegments]

/-- Every listed contact between a local old-incidence spoke and a local
implication route occurs at the spoke's ring-vertex tail. -/
theorem spokeRoute_meets_cycleRoute_only_at_tail
    (port : Port)
    (vertex : RingVertex)
    (literalIndex : Nat) :
    RoutesMeetOnlyAtFirstTail
      (spokeRoute port)
      (cycleRoute vertex literalIndex) := by
  rcases literalIndex with _ | literalIndex
  · cases port <;>
      cases vertex with
      | separator => native_decide
      | port cyclePort =>
          cases cyclePort <;> native_decide
  · rcases literalIndex with _ | literalIndex
    · cases port <;>
        cases vertex with
        | separator => native_decide
        | port cyclePort =>
            cases cyclePort <;> native_decide
    · simp [cycleRoute, RoutesMeetOnlyAtFirstTail]

/-- The tail-contact certificate also covers the total
presentation-indexed cycle lookup. -/
theorem spokeRoute_meets_cycleRoutes_only_at_tail
    (port : Port)
    (clauseIndex literalIndex : Nat) :
    RoutesMeetOnlyAtFirstTail
      (spokeRoute port)
      (cycleRoutes clauseIndex literalIndex) := by
  unfold cycleRoutes
  split
  · exact
      spokeRoute_meets_cycleRoute_only_at_tail
        port
        (presentedCycleVertices.getD
          clauseIndex .separator)
        literalIndex
  · simp [RoutesMeetOnlyAtFirstTail]

/-- Positive uniform scaling preserves mixed Figure 7 spoke/cycle
separation. -/
theorem scaledSpokeRoute_avoids_scaledCycleRoute
    (factor : Int)
    (factorPositive : 0 < factor)
    (port : Port)
    (vertex : RingVertex)
    (literalIndex : Nat) :
    RoutesAvoidEachOther
      (scalePolyline factor (spokeRoute port))
      (scalePolyline factor
        (cycleRoute vertex literalIndex)) := by
  exact
    RoutesAvoidEachOther.scalePolyline factorPositive
      (spokeRoute_avoids_cycleRoute
        port vertex literalIndex)

/-- A common translation preserves mixed scaled Figure 7 spoke/cycle
separation. -/
theorem translatedScaledSpokeRoute_avoids_translatedScaledCycleRoute
    (factor : Int)
    (factorPositive : 0 < factor)
    (offset : Cell)
    (port : Port)
    (vertex : RingVertex)
    (literalIndex : Nat) :
    RoutesAvoidEachOther
      ((scalePolyline factor (spokeRoute port)).map
        (Cell.add offset))
      ((scalePolyline factor
          (cycleRoute vertex literalIndex)).map
        (Cell.add offset)) := by
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      (scaledSpokeRoute_avoids_scaledCycleRoute
        factor factorPositive port vertex literalIndex)
      offset

end OccurrenceSplitRing
end LeanTrominoes

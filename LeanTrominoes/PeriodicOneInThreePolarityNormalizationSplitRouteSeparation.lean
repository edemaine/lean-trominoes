import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteFragments

/-!
# Separation of fragments cut from one refined route

For an incompatible literal, the first, reversed middle, and suffix
fragments partition one simple refined route.  The only listed contacts are
the two cut points, where both participating fragments advertise the point
as an endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private theorem routePointIsEndpoint_pair
    {first second point : Cell}
    (member : point ∈ [first, second]) :
    RoutePointIsEndpoint [first, second] point := by
  simp at member
  rcases member with rfl | rfl
  · left; rfl
  · right; rfl

/-- The first edge and reversed reserved middle edge meet only at their
common final cut point. -/
theorem prefix_middle_routesAvoidEachOther
    (route : List Cell)
    (length : 4 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    RoutesAvoidEachOther
      (RawRouteFragment.prefix.select route)
      (RawRouteFragment.middle.select route) := by
  let prefixSub := RawRouteFragment.endpointSubroute
    .prefix route length simple.1
  let middleSub := RawRouteFragment.endpointSubroute
    .middle route length simple.1
  have prefixPointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple prefixSub middleSub
  have middlePointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple middleSub prefixSub
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              cases rest with
              | nil => simp at length
              | cons fourth rest =>
                  apply routesAvoidEachOther_of_mem
                  · intro prefixSegment prefixSegmentMember
                      middleSegment middleSegmentMember
                    have prefixEq :
                        prefixSegment = GridSegment.mk first second := by
                      simpa [RawRouteFragment.select,
                        gridPolylineSegments] using prefixSegmentMember
                    have middleEq :
                        middleSegment = GridSegment.mk third second := by
                      simpa [RawRouteFragment.select,
                        gridPolylineSegments] using middleSegmentMember
                    subst prefixSegment
                    subst middleSegment
                    have sourceAvoid :=
                      simple.segmentInteriorsAvoid_of_mem
                        (first := GridSegment.mk first second)
                        (second := GridSegment.mk second third)
                        (by simp [gridPolylineSegments])
                        (by simp [gridPolylineSegments])
                        (by
                          intro equal
                          have firstEqSecond :=
                            congrArg GridSegment.start equal
                          change first = second at firstEqSecond
                          have firstFresh :=
                            (List.nodup_cons.mp simple.1).1
                          exact firstFresh
                            (by simp [firstEqSecond]))
                    intro meet
                    exact sourceAvoid
                      ((GridSegment.interiorsMeet_reverse_right_iff _ _).mp
                        meet)
                  · intro point pointMember segment segmentMember
                    exact prefixPointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro point pointMember segment segmentMember
                    exact middlePointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro prefixPoint prefixPointMember
                      middlePoint middlePointMember pointsEqual
                    change prefixPoint ∈ [first, second]
                      at prefixPointMember
                    change middlePoint ∈ [third, second]
                      at middlePointMember
                    exact ⟨routePointIsEndpoint_pair prefixPointMember,
                      routePointIsEndpoint_pair middlePointMember⟩

/-- The first edge and the suffix after the reserved points are completely
disjoint. -/
theorem prefix_suffix_routesAvoidEachOther
    (route : List Cell)
    (length : 4 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    RoutesAvoidEachOther
      (RawRouteFragment.prefix.select route)
      (RawRouteFragment.suffix.select route) := by
  let prefixSub := RawRouteFragment.endpointSubroute
    .prefix route length simple.1
  let suffixSub := RawRouteFragment.endpointSubroute
    .suffix route length simple.1
  have prefixPointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple prefixSub suffixSub
  have suffixPointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple suffixSub prefixSub
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              cases rest with
              | nil => simp at length
              | cons fourth rest =>
                  have firstFresh : first ∉ second :: third :: fourth :: rest :=
                    (List.nodup_cons.mp simple.1).1
                  have secondFresh : second ∉ third :: fourth :: rest :=
                    (List.nodup_cons.mp (List.nodup_cons.mp simple.1).2).1
                  apply routesAvoidEachOther_of_mem
                  · intro prefixSegment prefixSegmentMember
                      suffixSegment suffixSegmentMember
                    have prefixEq :
                        prefixSegment = GridSegment.mk first second := by
                      simpa [RawRouteFragment.select,
                        gridPolylineSegments] using prefixSegmentMember
                    subst prefixSegment
                    have suffixSourceMember : suffixSegment ∈
                        gridPolylineSegments
                          (first :: second :: third :: fourth :: rest) := by
                      exact List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ suffixSegmentMember)
                    have segmentsDifferent :
                        GridSegment.mk first second ≠ suffixSegment := by
                      intro equal
                      have endpoints :=
                        gridPolylineSegments_endpoints_mem suffixSegmentMember
                      apply firstFresh
                      exact List.mem_cons_of_mem second
                        (by
                          have startEq := congrArg GridSegment.start equal
                          change first = suffixSegment.start at startEq
                          rw [← startEq] at endpoints
                          exact endpoints.1)
                    exact simple.segmentInteriorsAvoid_of_mem
                      (by simp [gridPolylineSegments])
                      suffixSourceMember segmentsDifferent
                  · intro point pointMember segment segmentMember
                    exact prefixPointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro point pointMember segment segmentMember
                    exact suffixPointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro prefixPoint prefixPointMember
                      suffixPoint suffixPointMember pointsEqual
                    simp [RawRouteFragment.select] at prefixPointMember
                    simp only [RawRouteFragment.select, List.drop]
                      at suffixPointMember
                    rcases prefixPointMember with rfl | rfl
                    · apply (firstFresh (List.mem_cons_of_mem second ?_)).elim
                      exact pointsEqual.symm ▸ suffixPointMember
                    · apply (secondFresh ?_).elim
                      exact pointsEqual.symm ▸ suffixPointMember

/-- The reversed reserved middle edge and the remaining suffix meet only at
their common initial cut point. -/
theorem middle_suffix_routesAvoidEachOther
    (route : List Cell)
    (length : 4 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    RoutesAvoidEachOther
      (RawRouteFragment.middle.select route)
      (RawRouteFragment.suffix.select route) := by
  let middleSub := RawRouteFragment.endpointSubroute
    .middle route length simple.1
  let suffixSub := RawRouteFragment.endpointSubroute
    .suffix route length simple.1
  have middlePointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple middleSub suffixSub
  have suffixPointsAvoid :=
    routeIsSimple_endpointSubroutePointsAvoidInteriors
      simple suffixSub middleSub
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              cases rest with
              | nil => simp at length
              | cons fourth rest =>
                  have secondFresh : second ∉ third :: fourth :: rest :=
                    (List.nodup_cons.mp (List.nodup_cons.mp simple.1).2).1
                  apply routesAvoidEachOther_of_mem
                  · intro middleSegment middleSegmentMember
                      suffixSegment suffixSegmentMember
                    have middleEq :
                        middleSegment = GridSegment.mk third second := by
                      simpa [RawRouteFragment.select,
                        gridPolylineSegments] using middleSegmentMember
                    subst middleSegment
                    have suffixSourceMember : suffixSegment ∈
                        gridPolylineSegments
                          (first :: second :: third :: fourth :: rest) := by
                      exact List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ suffixSegmentMember)
                    have sourceSegmentsDifferent :
                        GridSegment.mk second third ≠ suffixSegment := by
                      intro equal
                      have endpoints :=
                        gridPolylineSegments_endpoints_mem suffixSegmentMember
                      apply secondFresh
                      have startEq := congrArg GridSegment.start equal
                      change second = suffixSegment.start at startEq
                      rw [← startEq] at endpoints
                      exact endpoints.1
                    have sourceAvoid := simple.segmentInteriorsAvoid_of_mem
                      (first := GridSegment.mk second third)
                      (second := suffixSegment)
                      (by simp [gridPolylineSegments])
                      suffixSourceMember sourceSegmentsDifferent
                    intro meet
                    exact sourceAvoid
                      ((GridSegment.interiorsMeet_reverse_left_iff _ _).mp
                        meet)
                  · intro point pointMember segment segmentMember
                    exact middlePointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro point pointMember segment segmentMember
                    exact suffixPointsAvoid.not_interior_of_mem
                      pointMember segmentMember
                  · intro middlePoint middlePointMember
                      suffixPoint suffixPointMember pointsEqual
                    simp [RawRouteFragment.select] at middlePointMember
                    simp only [RawRouteFragment.select, List.drop]
                      at suffixPointMember
                    rcases middlePointMember with middleEq | middleEq
                    · constructor
                      · left
                        change [third, second].head? = some middlePoint
                        exact congrArg some middleEq.symm
                      · left
                        change (third :: fourth :: rest).head? =
                          some suffixPoint
                        exact congrArg some
                          (middleEq.symm.trans pointsEqual)
                    · apply (secondFresh ?_).elim
                      have secondEqSuffix : second = suffixPoint :=
                        middleEq.symm.trans pointsEqual
                      exact secondEqSuffix.symm ▸ suffixPointMember

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

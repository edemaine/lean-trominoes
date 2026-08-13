/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointSubroutes
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSegmentOrigins

/-!
# Endpoint-respecting polarity-normalization route fragments

The four raw route shapes are the whole refined route, its first edge, the
reversed reserved middle edge, and the suffix after the two reserved points.
Each is an endpoint-respecting supported subroute of the complete refined
route.  Reversal changes only traversal direction, not geometric support.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Select the unshifted route fragment represented by raw segment
provenance. -/
def RawRouteFragment.select
    (fragment : RawRouteFragment) (route : List Cell) : List Cell :=
  match fragment with
  | .whole => route
  | .prefix => route.take 2
  | .middle => [route.getD 2 (0, 0), route.getD 1 (0, 0)]
  | .suffix => route.drop 2

/-- Every listed point of a selected raw fragment is a listed point of its
complete refined source route. -/
theorem RawRouteFragment.select_subset
    (fragment : RawRouteFragment)
    (route : List Cell)
    (length : 4 ≤ route.length) :
    ∀ {point}, point ∈ fragment.select route → point ∈ route := by
  intro point pointMember
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
                  cases fragment with
                  | whole => exact pointMember
                  | «prefix» =>
                      simp [RawRouteFragment.select] at pointMember
                      rcases pointMember with rfl | rfl <;> simp
                  | middle =>
                      simp [RawRouteFragment.select] at pointMember
                      rcases pointMember with rfl | rfl <;> simp
                  | suffix =>
                      simp only [RawRouteFragment.select,
                        List.drop] at pointMember ⊢
                      exact List.mem_cons_of_mem first
                        (List.mem_cons_of_mem second pointMember)

/-- Prefix and middle fragments use only the clause endpoint and the first
two reserved subdivision points. -/
theorem RawRouteFragment.select_mem_getD_zero_one_two
    (fragment : RawRouteFragment)
    (route : List Cell)
    (length : 4 ≤ route.length)
    (nearClause : fragment = .prefix ∨ fragment = .middle)
    {point : Cell}
    (pointMember : point ∈ fragment.select route) :
    point = route.getD 0 (0, 0) ∨
      point = route.getD 1 (0, 0) ∨
      point = route.getD 2 (0, 0) := by
  rcases nearClause with rfl | rfl
  · cases route with
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
                    simp [RawRouteFragment.select] at pointMember
                    rcases pointMember with rfl | rfl <;> simp
  · cases route with
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
                    simp [RawRouteFragment.select] at pointMember
                    rcases pointMember with rfl | rfl <;> simp

/-- Every raw route shape is supported on its complete refined source route,
and retained source endpoints remain endpoints of the selected fragment. -/
theorem RawRouteFragment.endpointSubroute
    (fragment : RawRouteFragment)
    (route : List Cell)
    (length : 4 ≤ route.length)
    (nodup : route.Nodup) :
    EndpointSubroute (fragment.select route) route := by
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
                  cases fragment with
                  | whole => exact EndpointSubroute.refl _
                  | «prefix» =>
                      constructor
                      · intro point pointMember
                        simp [RawRouteFragment.select] at pointMember
                        rcases pointMember with rfl | rfl <;> simp
                      · intro segment segmentMember
                        have segmentEq :
                            segment = GridSegment.mk first second := by
                          simpa [RawRouteFragment.select,
                            gridPolylineSegments] using segmentMember
                        subst segment
                        exact ⟨GridSegment.mk first second,
                          by simp [gridPolylineSegments], Or.inl rfl⟩
                      · intro point pointMember sourceEndpoint
                        simp [RawRouteFragment.select] at pointMember
                        rcases pointMember with rfl | rfl
                        · left; rfl
                        · right; rfl
                  | middle =>
                      constructor
                      · intro point pointMember
                        simp [RawRouteFragment.select] at pointMember
                        rcases pointMember with rfl | rfl <;> simp
                      · intro segment segmentMember
                        have segmentEq :
                            segment = GridSegment.mk third second := by
                          simpa [RawRouteFragment.select,
                            gridPolylineSegments] using segmentMember
                        subst segment
                        exact ⟨GridSegment.mk second third,
                          by simp [gridPolylineSegments], Or.inr rfl⟩
                      · intro point pointMember sourceEndpoint
                        simp [RawRouteFragment.select] at pointMember
                        rcases pointMember with rfl | rfl
                        · left; rfl
                        · right; rfl
                  | suffix =>
                      constructor
                      · intro point pointMember
                        simp only [RawRouteFragment.select,
                          List.drop] at pointMember ⊢
                        exact List.mem_cons_of_mem first
                          (List.mem_cons_of_mem second pointMember)
                      · intro segment segmentMember
                        refine ⟨segment, ?_, Or.inl rfl⟩
                        simp only [RawRouteFragment.select] at segmentMember
                        rw [gridPolylineSegments_drop_two] at segmentMember
                        exact List.mem_of_mem_drop segmentMember
                      · intro point pointMember sourceEndpoint
                        simp only [RawRouteFragment.select,
                          List.drop] at pointMember ⊢
                        rcases sourceEndpoint with sourceHead | sourceLast
                        · have firstEq : first = point := by
                            simpa using Option.some.inj sourceHead
                          subst point
                          have firstFresh := (List.nodup_cons.mp nodup).1
                          exact (firstFresh
                            (by exact List.mem_cons_of_mem second pointMember)).elim
                        · right
                          simpa using sourceLast

/-- Selecting any of the four raw fragments preserves route-local
simplicity. -/
theorem RawRouteFragment.routeIsSimple
    (fragment : RawRouteFragment)
    (route : List Cell)
    (length : 4 ≤ route.length)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple (fragment.select route) := by
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
                  cases fragment with
                  | whole => exact simple
                  | «prefix» =>
                      have subroute := RawRouteFragment.endpointSubroute
                        .prefix (first :: second :: third :: fourth :: rest)
                        length simple.1
                      refine ⟨?_, ?_, ?_⟩
                      · have firstNeSecond : first ≠ second := by
                          intro equal
                          exact (List.nodup_cons.mp simple.1).1
                            (by simp [equal])
                        simp [RawRouteFragment.select, firstNeSecond]
                      · intro point pointMember segment segmentMember
                        exact
                          (routeIsSimple_endpointSubroutePointsAvoidInteriors
                            simple subroute subroute).not_interior_of_mem
                              pointMember segmentMember
                      · intro firstSegment firstMember
                          secondSegment secondMember indicesDifferent
                        simp [RawRouteFragment.select,
                          gridPolylineSegments] at firstMember secondMember
                        subst firstSegment
                        subst secondSegment
                        exact (indicesDifferent rfl).elim
                  | middle =>
                      have subroute := RawRouteFragment.endpointSubroute
                        .middle (first :: second :: third :: fourth :: rest)
                        length simple.1
                      refine ⟨?_, ?_, ?_⟩
                      · have secondNeThird : second ≠ third := by
                          intro equal
                          exact (List.nodup_cons.mp
                            (List.nodup_cons.mp simple.1).2).1
                              (by simp [equal])
                        simp [RawRouteFragment.select, secondNeThird,
                          Ne.symm secondNeThird]
                      · intro point pointMember segment segmentMember
                        exact
                          (routeIsSimple_endpointSubroutePointsAvoidInteriors
                            simple subroute subroute).not_interior_of_mem
                              pointMember segmentMember
                      · intro firstSegment firstMember
                          secondSegment secondMember indicesDifferent
                        simp [RawRouteFragment.select,
                          gridPolylineSegments] at firstMember secondMember
                        subst firstSegment
                        subst secondSegment
                        exact (indicesDifferent rfl).elim
                  | suffix =>
                      simpa [RawRouteFragment.select, List.drop] using
                        simple.tail.tail

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

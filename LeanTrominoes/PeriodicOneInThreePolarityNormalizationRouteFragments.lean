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

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

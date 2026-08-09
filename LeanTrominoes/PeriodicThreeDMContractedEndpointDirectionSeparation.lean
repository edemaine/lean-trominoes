import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.PeriodicThreeDMContractedEndpointRays

/-!
# Direction separation at contracted 3DM vertices

Distinct contracted endpoint occurrences at one vertex leave in distinct
cardinal directions.  Each endpoint ray is an actual lifted occurrence of a
stored segment.  Equal directions would therefore make the two ray interiors
overlap immediately outside their common start, contrary to continuous
planarity of the contracted drawing.
-/

namespace LeanTrominoes

open Gadget

namespace GridSegment

/-- Segment-valued form of `interiorsMeet_of_same_start_direction`. -/
theorem interiorsMeet_of_same_start_direction'
    {first second : GridSegment}
    (firstAligned : first.IsAxisAligned)
    (secondAligned : second.IsAxisAligned)
    (sameStart : first.start = second.start)
    (sameDirection :
      AxisDirection.between first.start first.finish =
        AxisDirection.between second.start second.finish) :
    first.InteriorsMeet second := by
  rcases first with ⟨firstStart, firstFinish⟩
  rcases second with ⟨secondStart, secondFinish⟩
  change firstStart = secondStart at sameStart
  subst secondStart
  exact interiorsMeet_of_same_start_direction
    firstAligned secondAligned sameDirection

end GridSegment

namespace PeriodicThreeDM

/-- The source/target enumeration of duplicate-free contracted edges is
itself duplicate-free. -/
theorem contractedEndpoints_nodup
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    problem.contractedEndpoints.Nodup := by
  unfold contractedEndpoints
  rw [List.nodup_flatMap]
  constructor
  · intro edge edgeMember
    simp
  · exact (contractedEdges_nodup problem degree).imp fun
      {first second} different => by
        apply List.disjoint_left.mpr
        intro endpoint firstMember secondMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
        rcases firstMember with rfl | rfl
        · rcases secondMember with equal | equal
          · exact different (ContractedEndpoint.source.inj equal)
          · cases equal
        · rcases secondMember with equal | equal
          · cases equal
          · exact different (ContractedEndpoint.target.inj equal)

/-- Filtering the endpoint enumeration down to one vertex preserves
duplicate-freeness. -/
theorem contractedEndpointsAt_nodup
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    (vertex : PeriodicThreeDMVertex) :
    (problem.contractedEndpointsAt vertex).Nodup := by
  exact (contractedEndpoints_nodup problem degree).filter _

/-- Distinct endpoints incident to one loopless contracted vertex belong to
distinct contracted edges. -/
theorem ContractedEndpoint.edge_ne_of_ne_of_vertex_eq
    {problem : PeriodicThreeDM}
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.edge ≠ second.edge := by
  intro sameEdge
  cases first with
  | source firstEdge =>
      cases second with
      | source secondEdge =>
          simp only [ContractedEndpoint.edge_source] at sameEdge
          subst secondEdge
          exact different rfl
      | target secondEdge =>
          simp only [ContractedEndpoint.edge_source,
            ContractedEndpoint.edge_target] at sameEdge
          subst secondEdge
          have edgeMember :=
            (ContractedEndpoint.source firstEdge).edge_mem_of_mem firstMember
          have graphEdgeMember : firstEdge.toPeriodicEdge ∈
              problem.contractedGraph.edges :=
            List.mem_map.mpr ⟨firstEdge, edgeMember, rfl⟩
          have loopless :=
            contractedGraph_edgesAreLoopless problem degree
              firstEdge.toPeriodicEdge graphEdgeMember
          apply loopless
          exact sameVertex
  | target firstEdge =>
      cases second with
      | source secondEdge =>
          simp only [ContractedEndpoint.edge_target,
            ContractedEndpoint.edge_source] at sameEdge
          subst secondEdge
          have edgeMember :=
            (ContractedEndpoint.target firstEdge).edge_mem_of_mem firstMember
          have graphEdgeMember : firstEdge.toPeriodicEdge ∈
              problem.contractedGraph.edges :=
            List.mem_map.mpr ⟨firstEdge, edgeMember, rfl⟩
          have loopless :=
            contractedGraph_edgesAreLoopless problem degree
              firstEdge.toPeriodicEdge graphEdgeMember
          apply loopless
          exact sameVertex.symm
      | target secondEdge =>
          simp only [ContractedEndpoint.edge_target] at sameEdge
          subst secondEdge
          exact different rfl

/-- Distinct endpoint rays at the same contracted vertex have distinct
outward directions. -/
theorem ContractedEndpoint.outwardDirection_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.outwardDirection presentation.toPlanarPresentation ≠
      second.outwardDirection presentation.toPlanarPresentation := by
  rcases first.exists_ray presentation.toPlanarPresentation degree
      firstMember with ⟨firstRay⟩
  rcases second.exists_ray presentation.toPlanarPresentation degree
      secondMember with ⟨secondRay⟩
  have edgesDifferent : first.edge ≠ second.edge :=
    ContractedEndpoint.edge_ne_of_ne_of_vertex_eq degree
      firstMember secondMember different sameVertex
  have routeIndicesDifferent :
      problem.contractedEdges.idxOf first.edge ≠
        problem.contractedEdges.idxOf second.edge := by
    intro indicesEqual
    apply edgesDifferent
    exact (List.idxOf_inj (first.edge_mem_of_mem firstMember)).mp
      indicesEqual
  have indexedRouteIndicesDifferent :
      firstRay.indexed.routeIndex ≠ secondRay.indexed.routeIndex := by
    rw [firstRay.routeIndex_eq, secondRay.routeIndex_eq]
    exact routeIndicesDifferent
  have keysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstRay.indexed firstRay.translate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondRay.indexed secondRay.translate := by
    intro keysEqual
    apply indexedRouteIndicesDifferent
    exact congrArg Prod.fst keysEqual
  intro directionsEqual
  have realizedMeet :
      firstRay.realized.InteriorsMeet secondRay.realized :=
    GridSegment.interiorsMeet_of_same_start_direction'
      firstRay.realized_isAxisAligned
      secondRay.realized_isAxisAligned
      (firstRay.realized_start.trans
        (sameVertex ▸ secondRay.realized_start.symm))
      (firstRay.realized_direction.trans
        (directionsEqual.trans secondRay.realized_direction.symm))
  have originalMeet :
      GridSegment.InteriorsMeet
        (firstRay.indexed.segment.translate
          (presentation.contractedDrawing.periodTranslation
            firstRay.translate))
        (secondRay.indexed.segment.translate
          (presentation.contractedDrawing.periodTranslation
            secondRay.translate)) := by
    cases firstReversed : firstRay.reversed <;>
      cases secondReversed : secondRay.reversed <;>
      simpa [ContractedEndpointRay.realized,
        ContractedEndpointRay.traversalSegment,
        firstReversed, secondReversed] using realizedMeet
  exact
    (presentation.contractedDrawing_isContinuouslyPlanar degree
      |>.noInteriorsMeet firstRay.indexedMember secondRay.indexedMember
        keysDifferent) originalMeet

end PeriodicThreeDM
end LeanTrominoes

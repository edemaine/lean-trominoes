import LeanTrominoes.PeriodicThreeDMVertexNormalizationOccurrences
import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Separation of local degree-three normalization templates

The Figure 2 templates are finite, so their same-center geometry is checked
exactly.  Their points all lie in coordinate radius three of the local
center.  Because distinct old lattice points become twelve cells apart,
the general scaled-neighborhood theorem then gives strict separation for
templates based at distinct old points.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace DegreeThreeVertexNormalization

set_option maxHeartbeats 1000000 in
/-- Two distinct routes in one Figure 2 template satisfy the full
continuous endpoint-contact separation predicate. -/
theorem routes_avoidEachOther
    (omitted : VertexSide)
    {first second : CanonicalVertexPort}
    (different : first ≠ second) :
    RoutesAvoidEachOther
      (route omitted first) (route omitted second) := by
  cases omitted <;> cases first <;> cases second <;>
    simp_all <;> native_decide

/-- Every contact of two distinct Figure 2 routes is their common head at
the template center. -/
theorem routes_meetOnlyAtHeads
    (omitted : VertexSide)
    {first second : CanonicalVertexPort}
    (different : first ≠ second) :
    RoutesMeetOnlyAtHeads
      (route omitted first) (route omitted second) := by
  intro firstPoint firstMember secondPoint secondMember equal
  subst secondPoint
  have atCenter := routes_meetOnlyAtCenter omitted
    first second different firstPoint firstMember secondMember
  subst firstPoint
  exact ⟨(route_endpoints omitted first).1,
    (route_endpoints omitted second).1⟩

/-- Every listed point of a Figure 2 route lies within coordinate radius
three of its center. -/
theorem route_withinCoordinateRadius
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    ∀ point ∈ route omitted port,
      WithinCoordinateRadius 3 center point := by
  cases omitted <;> cases port <;>
    native_decide

end DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Anchoring a Figure 2 route at an old lattice point gives a radius-three
route around the corresponding normalized vertex. -/
theorem normalizationTemplateAt_route_withinCoordinateRadius
    (position : Cell) (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    ∀ point ∈ normalizationTemplateAt position (route omitted port),
      WithinCoordinateRadius 3
        (normalizeVertexPosition position) point := by
  intro point pointMember
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact
    (DegreeThreeVertexNormalization.route_withinCoordinateRadius
      omitted port localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position)

/-- Figure 2 routes at distinct old lattice positions are contact-free:
their radius-three boxes have six cells of clearance after scale twelve. -/
theorem normalizationTemplateAt_routes_strictlyAvoid_of_positions_ne
    {firstPosition secondPosition : Cell}
    (positionsDifferent : firstPosition ≠ secondPosition)
    (firstOmitted secondOmitted : VertexSide)
    (firstPort secondPort : CanonicalVertexPort) :
    RoutesStrictlyAvoidEachOther
      (normalizationTemplateAt firstPosition
        (route firstOmitted firstPort))
      (normalizationTemplateAt secondPosition
        (route secondOmitted secondPort)) := by
  apply
    routesStrictlyAvoidEachOther_of_distinct_offsetScaledCoordinateNeighborhoods
      (firstCenter := firstPosition)
      (secondCenter := secondPosition)
      (offset := center)
      (factor := 12) (radius := 3)
      positionsDifferent (by decide) (by decide)
  · simpa [normalizeVertexPosition, vertexNormalizationScale,
      Cell.add] using
      normalizationTemplateAt_route_withinCoordinateRadius
        firstPosition firstOmitted firstPort
  · simpa [normalizeVertexPosition, vertexNormalizationScale,
      Cell.add] using
      normalizationTemplateAt_route_withinCoordinateRadius
        secondPosition secondOmitted secondPort

/-- Distinct endpoint directions at one contracted vertex are sent to
distinct canonical ports by the first replacement round. -/
theorem ContractedEndpoint.firstNormalizedPort_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.firstNormalizedPort presentation.toPlanarPresentation ≠
      second.firstNormalizedPort presentation.toPlanarPresentation := by
  let planar := presentation.toPlanarPresentation
  have sidesDifferent :
      first.outwardSide planar ≠ second.outwardSide planar :=
    first.outwardSide_ne presentation degree
      firstMember secondMember different sameVertex
  have firstUsed := first.outwardSide_ne_omittedSideAt
    presentation wellFormed degree firstMember
  have secondUsed := second.outwardSide_ne_omittedSideAt
    presentation wellFormed degree secondMember
  intro portsEqual
  apply sidesDifferent
  have boundaryEqual := congrArg
    (boundarySide (omittedSideAt planar first.vertex)) portsEqual
  unfold ContractedEndpoint.firstNormalizedPort at boundaryEqual
  rw [boundarySide_canonicalPortForSide _ _ firstUsed] at boundaryEqual
  rw [sameVertex] at boundaryEqual firstUsed
  rw [boundarySide_canonicalPortForSide _ _ secondUsed] at boundaryEqual
  exact boundaryEqual

/-- The selected first-round templates of distinct endpoints at one vertex
satisfy full separation and can meet only at the new vertex center. -/
theorem ContractedEndpoint.firstNormalizationTemplates_avoid_at_sameVertex
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    let planar := presentation.toPlanarPresentation
    RoutesAvoidEachOther
        (first.firstNormalizationTemplate planar)
        (second.firstNormalizationTemplate planar) ∧
      RoutesMeetOnlyAtHeads
        (first.firstNormalizationTemplate planar)
        (second.firstNormalizationTemplate planar) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have portsDifferent := first.firstNormalizedPort_ne
    presentation wellFormed degree firstMember secondMember
      different sameVertex
  unfold ContractedEndpoint.firstNormalizationTemplate
  rw [sameVertex]
  exact
    ⟨DegreeThreeVertexNormalization.routes_avoidEachOther
        (omittedSideAt planar second.vertex) portsDifferent,
      DegreeThreeVertexNormalization.routes_meetOnlyAtHeads
        (omittedSideAt planar second.vertex) portsDifferent⟩

end PeriodicThreeDM
end LeanTrominoes

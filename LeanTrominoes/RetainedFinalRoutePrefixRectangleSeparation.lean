import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedOrthogonalPrefixes
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup
import LeanTrominoes.RetainedFinalRoutePrefixSeparation
import LeanTrominoes.RetainedRayRasterizationSeparation

/-!
# Rectangle separation of final retained route prefixes

The final retained planar-SAT drawing already proves strict continuous
separation between the `dropLast` prefixes of distinct stored routes.  The
route-shape certificate proves that both such prefixes are orthogonal.
Together these facts imply the integral point/segment and segment/segment
rectangle separation used by retained-ray rasterization.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 2000000

/-- A flat route membership recovers the positioned incidence metadata
needed to apply final route-prefix orthogonality. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixOrthogonal_of_mem_edgeRoutes
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {route : List Cell}
    {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx) :
    OrthogonalPolyline route.dropLast := by
  let source :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula
  let routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  rcases
      @PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        source placement routes
        (route, routeIndex) routeMember with
    ⟨incidence, _incidenceMember,
      clause, literal,
      clauseMember, literalMember,
      routeEq, _routeIndexEq⟩
  have routeEq' :
      route =
        routes incidence.1.clauseIndex
          incidence.1.literalIndex := by
    simpa using routeEq
  have orthogonal :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_prefixOrthogonal
      formula wellFormed degree isLocal clausesNonempty
      (clause, incidence.1.clauseIndex)
      clauseMember
      (literal, incidence.1.literalIndex)
      literalMember
  rw [routeEq']
  simpa [routes] using orthogonal

/-- Distinct final retained source routes with different clause endpoints
have pairwise-separated integral rectangles throughout both prefixes. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_sourcePolylineRectanglesSeparated
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (first, firstIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (second, secondIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (headsDifferent : first.head? ≠ second.head?) :
    SourcePolylineRectanglesSeparated
      first.dropLast second.dropLast := by
  have firstOrthogonal :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixOrthogonal_of_mem_edgeRoutes
      formula wellFormed degree isLocal clausesNonempty
      firstMember
  have secondOrthogonal :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixOrthogonal_of_mem_edgeRoutes
      formula wellFormed degree isLocal clausesNonempty
      secondMember
  have avoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  exact
    SourcePolylineRectanglesSeparated.of_strictlyAvoid
      firstOrthogonal secondOrthogonal avoid

/-- If the reference route's discarded final segment is axis-aligned, the
prefix/prefix rectangle certificate extends across that last segment to the
complete reference route. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_sourcePolylineRectanglesSeparated_of_finalSegmentAxisAligned
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondTarget : Cell}
    (firstMember :
      (first, firstIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (second, secondIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (headsDifferent : first.head? ≠ second.head?)
    (firstHead : first.head? = some firstSource)
    (secondLast : second.getLast? = some secondTarget)
    (sourceNeTarget : firstSource ≠ secondTarget)
    (finalSegmentAxisAligned :
      (⟨polylineLastEntrance second, secondTarget⟩ :
        GridSegment).IsAxisAligned) :
    SourcePolylineRectanglesSeparated
      first.dropLast second := by
  have prefixSeparated :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_sourcePolylineRectanglesSeparated
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  have firstPrefixOrthogonal :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixOrthogonal_of_mem_edgeRoutes
      formula wellFormed degree isLocal clausesNonempty
      firstMember
  have finalPolylineOrthogonal :
      OrthogonalPolyline
        [polylineLastEntrance second, secondTarget] := by
    simpa [OrthogonalPolyline] using
      finalSegmentAxisAligned
  have finalAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherFinalSegment
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      sourceNeTarget
  have finalSeparated :
      SourcePolylineRectanglesSeparated
        first.dropLast
        [polylineLastEntrance second, secondTarget] :=
    SourcePolylineRectanglesSeparated.of_strictlyAvoid
      firstPrefixOrthogonal finalPolylineOrthogonal
      finalAvoid
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length
      second secondLength
  have secondEntrance :
      second.dropLast.getLast? =
        some (polylineLastEntrance second) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  exact
    SourcePolylineRectanglesSeparated.of_dropLast_and_finalSegment
      secondEntrance secondLast
      prefixSeparated finalSeparated

end PeriodicOrthocrossing
end LeanTrominoes

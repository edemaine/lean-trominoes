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

/-- Strict separation of two complete routes turns axis alignment of their
discarded final segments into separation of the corresponding integral
endpoint rectangles. -/
theorem finalSegment_coordinateRectanglesSeparated_of_strictlyAvoid
    {first second : List Cell}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstAligned :
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (strict :
      RoutesStrictlyAvoidEachOther first second) :
    ClosedGridRectanglesSeparated
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).coordinateUpper := by
  let firstFinal : GridSegment :=
    ⟨polylineLastEntrance first, first.getLastD (0, 0)⟩
  let secondFinal : GridSegment :=
    ⟨polylineLastEntrance second, second.getLastD (0, 0)⟩
  have firstMember :
      firstFinal ∈ gridPolylineSegments first := by
    exact finalGridSegment_mem first firstLength
  have secondMember :
      secondFinal ∈ gridPolylineSegments second := by
    exact finalGridSegment_mem second secondLength
  have firstEndpoints :=
    gridPolylineSegments_endpoints_mem firstMember
  have secondEndpoints :=
    gridPolylineSegments_endpoints_mem secondMember
  exact
    GridSegment.coordinateRectangles_separated_of_axisAligned
      firstAligned secondAligned
      (strict.1 firstFinal firstMember
        secondFinal secondMember)
      (strict.2.1 firstFinal.start firstEndpoints.1
        secondFinal secondMember)
      (strict.2.1 firstFinal.finish firstEndpoints.2
        secondFinal secondMember)
      (strict.2.2.1 secondFinal.start secondEndpoints.1
        firstFinal firstMember)
      (strict.2.2.1 secondFinal.finish secondEndpoints.2
        firstFinal firstMember)
      (strict.2.2.2 firstFinal.start firstEndpoints.1
        secondFinal.start secondEndpoints.1)
      (strict.2.2.2 firstFinal.start firstEndpoints.1
        secondFinal.finish secondEndpoints.2)
      (strict.2.2.2 firstFinal.finish firstEndpoints.2
        secondFinal.start secondEndpoints.1)
      (strict.2.2.2 firstFinal.finish firstEndpoints.2
        secondFinal.finish secondEndpoints.2)

/-- For two different final retained routes with four distinct advertised
endpoint pairs, axis-aligned last segments have separated integral endpoint
rectangles. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_finalSegmentRectanglesSeparated_of_axisAligned
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
    (headHeadNe : first.head? ≠ second.head?)
    (headLastNe : first.head? ≠ second.getLast?)
    (lastHeadNe : first.getLast? ≠ second.head?)
    (lastLastNe : first.getLast? ≠ second.getLast?)
    (firstAligned :
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned) :
    ClosedGridRectanglesSeparated
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance first,
          first.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance second,
          second.getLastD (0, 0)⟩ : GridSegment).coordinateUpper := by
  apply finalSegment_coordinateRectanglesSeparated_of_strictlyAvoid
    firstLength secondLength firstAligned secondAligned
  exact
    retainedDeduplicatedGaugedWrappedDrawing_routesStrictlyAvoidEachOther_of_endpoints_ne
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headHeadNe headLastNe lastHeadNe lastLastNe

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

/-- A flat route membership also recovers the final
orthogonal-or-singleton-prefix dichotomy. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routeOrthogonalOrSingletonPrefix_of_mem_edgeRoutes
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
    OrthogonalPolyline route ∨
      route.dropLast.length = 1 := by
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
  have shape :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_orthogonalOrSingletonPrefix
      formula wellFormed degree isLocal clausesNonempty
      (clause, incidence.1.clauseIndex)
      clauseMember
      (literal, incidence.1.literalIndex)
      literalMember
  rw [routeEq']
  simpa [routes] using shape

/-- A genuine final route with a non-axis-aligned last segment must select
the direct-style branch and therefore has a singleton prefix. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_length_eq_one_of_finalSegment_not_axisAligned
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
    {target : Cell}
    (routeMember :
      (route, routeIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (routeLength : 2 ≤ route.length)
    (routeLast : route.getLast? = some target)
    (finalSegmentNotAxisAligned :
      ¬(⟨polylineLastEntrance route, target⟩ :
        GridSegment).IsAxisAligned) :
    route.dropLast.length = 1 := by
  rcases
      retainedDeduplicatedGaugedWrappedDrawing_routeOrthogonalOrSingletonPrefix_of_mem_edgeRoutes
        formula wellFormed degree isLocal clausesNonempty
        routeMember with
    orthogonal | singleton
  · exfalso
    apply finalSegmentNotAxisAligned
    have finalMember :=
      finalGridSegment_mem route routeLength
    have aligned :=
      (orthogonalPolyline_iff_segments route).mp
        orthogonal
        (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment)
        finalMember
    have lastD :
        route.getLastD (0, 0) = target := by
      rw [List.getLastD_eq_getLast?, routeLast, Option.getD_some]
    rw [lastD] at aligned
    exact aligned
  · exact singleton

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

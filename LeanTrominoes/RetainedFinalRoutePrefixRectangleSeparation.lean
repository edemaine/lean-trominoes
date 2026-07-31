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

/-- A duplicate-free nonempty list whose head and last point coincide is a
singleton. -/
private theorem list_length_eq_one_of_nodup_of_head_last_eq
    {α : Type*} {points : List α} {point : α}
    (nodup : points.Nodup)
    (headEq : points.head? = some point)
    (lastEq : points.getLast? = some point) :
    points.length = 1 := by
  cases points with
  | nil =>
      simp at headEq
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at headEq
      subst head
      by_cases tailEmpty : tail = []
      · simp [tailEmpty]
      · have tailLast : tail.getLast? = some point := by
          rw [← List.getLast?_cons_of_ne_nil tailEmpty]
          exact lastEq
        exact
          ((List.nodup_cons.mp nodup).1
            (List.mem_of_getLast? tailLast)).elim

/-- Ordinary route planarity also strictly separates the two discarded
terminal segments when the routes have no cross-endpoint contact and their
retained prefixes are not both singletons.  The latter condition rules out
the only contact still permitted by ordinary planarity: both penultimate
points being the common route head. -/
theorem
    finalSegment_coordinateRectanglesSeparated_of_avoid_of_not_both_singletonPrefixes
    {first second : List Cell}
    {firstEntrance secondEntrance firstLast secondLast : Cell}
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup)
    (avoid : RoutesAvoidEachOther first second)
    (firstEntranceEq :
      first.dropLast.getLast? = some firstEntrance)
    (secondEntranceEq :
      second.dropLast.getLast? = some secondEntrance)
    (firstLastEq : first.getLast? = some firstLast)
    (secondLastEq : second.getLast? = some secondLast)
    (headLastNe : first.head? ≠ second.getLast?)
    (lastHeadNe : first.getLast? ≠ second.head?)
    (lastLastNe : first.getLast? ≠ second.getLast?)
    (notBothSingleton :
      ¬(first.dropLast.length = 1 ∧
        second.dropLast.length = 1))
    (firstAligned :
      (⟨firstEntrance, firstLast⟩ :
        GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨secondEntrance, secondLast⟩ :
        GridSegment).IsAxisAligned) :
    ClosedGridRectanglesSeparated
      (⟨firstEntrance, firstLast⟩ :
        GridSegment).coordinateLower
      (⟨firstEntrance, firstLast⟩ :
        GridSegment).coordinateUpper
      (⟨secondEntrance, secondLast⟩ :
        GridSegment).coordinateLower
      (⟨secondEntrance, secondLast⟩ :
        GridSegment).coordinateUpper := by
  let firstFinal : GridSegment :=
    ⟨firstEntrance, firstLast⟩
  let secondFinal : GridSegment :=
    ⟨secondEntrance, secondLast⟩
  have firstDropNonempty : first.dropLast ≠ [] := by
    intro empty
    rw [empty] at firstEntranceEq
    simp at firstEntranceEq
  have secondDropNonempty : second.dropLast ≠ [] := by
    intro empty
    rw [empty] at secondEntranceEq
    simp at secondEntranceEq
  have firstDecomposition :
      first.dropLast ++ [firstLast] = first :=
    List.dropLast_append_getLast? firstLast firstLastEq
  have secondDecomposition :
      second.dropLast ++ [secondLast] = second :=
    List.dropLast_append_getLast? secondLast secondLastEq
  have firstEntranceLastD :
      first.dropLast.getLastD (0, 0) = firstEntrance := by
    rw [List.getLastD_eq_getLast?, firstEntranceEq]
    simp
  have secondEntranceLastD :
      second.dropLast.getLastD (0, 0) = secondEntrance := by
    rw [List.getLastD_eq_getLast?, secondEntranceEq]
    simp
  have firstFinalMember :
      firstFinal ∈ gridPolylineSegments first := by
    rw [← firstDecomposition,
      gridPolylineSegments_append_singleton_of_ne_nil
        first.dropLast (0, 0) firstLast firstDropNonempty,
      List.mem_append]
    apply Or.inr
    simp only [List.mem_singleton]
    simpa [firstFinal] using firstEntranceLastD.symm
  have secondFinalMember :
      secondFinal ∈ gridPolylineSegments second := by
    rw [← secondDecomposition,
      gridPolylineSegments_append_singleton_of_ne_nil
        second.dropLast (0, 0) secondLast secondDropNonempty,
      List.mem_append]
    apply Or.inr
    simp only [List.mem_singleton]
    simpa [secondFinal] using secondEntranceLastD.symm
  have firstEntranceMember :
      firstEntrance ∈ first.dropLast :=
    List.mem_of_getLast? firstEntranceEq
  have secondEntranceMember :
      secondEntrance ∈ second.dropLast :=
    List.mem_of_getLast? secondEntranceEq
  have firstPrefixNodup : first.dropLast.Nodup := by
    have appended :
        (first.dropLast ++ [firstLast]).Nodup := by
      rw [firstDecomposition]
      exact firstNodup
    exact appended.of_append_left
  have secondPrefixNodup : second.dropLast.Nodup := by
    have appended :
        (second.dropLast ++ [secondLast]).Nodup := by
      rw [secondDecomposition]
      exact secondNodup
    exact appended.of_append_left
  have firstFinalEndpoints :=
    gridPolylineSegments_endpoints_mem firstFinalMember
  have secondFinalEndpoints :=
    gridPolylineSegments_endpoints_mem secondFinalMember
  have contactsAtEndpoints :
      ∀ {firstPoint secondPoint : Cell},
        firstPoint ∈ first →
        secondPoint ∈ second →
        firstPoint = secondPoint →
          RoutePointIsEndpoint first firstPoint ∧
            RoutePointIsEndpoint second secondPoint := by
    intro firstPoint secondPoint firstMember secondMember equal
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstIndex, firstIndexed⟩
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondIndex, secondIndexed⟩
    have indexedEqual :
        first.get firstIndex = second.get secondIndex := by
      rw [firstIndexed, secondIndexed]
      exact equal
    have endpoints :=
      avoid.2.2.2 firstIndex secondIndex indexedEqual
    rw [firstIndexed, secondIndexed] at endpoints
    exact endpoints
  have finalRoutesStrict :
      RoutesStrictlyAvoidEachOther
        [firstEntrance, firstLast]
        [secondEntrance, secondLast] := by
    unfold RoutesStrictlyAvoidEachOther
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro firstSegment firstSegmentMember
        secondSegment secondSegmentMember
      have firstSegmentEq : firstSegment = firstFinal := by
        simpa [gridPolylineSegments, firstFinal] using
          firstSegmentMember
      have secondSegmentEq : secondSegment = secondFinal := by
        simpa [gridPolylineSegments, secondFinal] using
          secondSegmentMember
      subst firstSegment
      subst secondSegment
      exact avoid.segmentsAvoid_of_mem
        firstFinal firstFinalMember secondFinal secondFinalMember
    · intro firstPoint firstPointMember
        secondSegment secondSegmentMember
      have firstPointOriginal : firstPoint ∈ first := by
        simp at firstPointMember
        rcases firstPointMember with rfl | rfl
        · exact List.mem_of_mem_dropLast firstEntranceMember
        · exact firstFinalEndpoints.2
      have secondSegmentEq : secondSegment = secondFinal := by
        simpa [gridPolylineSegments, secondFinal] using
          secondSegmentMember
      subst secondSegment
      exact avoid.firstPointsAvoid_of_mem
        firstPoint firstPointOriginal secondFinal secondFinalMember
    · intro secondPoint secondPointMember
        firstSegment firstSegmentMember
      have secondPointOriginal : secondPoint ∈ second := by
        simp at secondPointMember
        rcases secondPointMember with rfl | rfl
        · exact List.mem_of_mem_dropLast secondEntranceMember
        · exact secondFinalEndpoints.2
      have firstSegmentEq : firstSegment = firstFinal := by
        simpa [gridPolylineSegments, firstFinal] using
          firstSegmentMember
      subst firstSegment
      exact avoid.secondPointsAvoid_of_mem
        secondPoint secondPointOriginal firstFinal firstFinalMember
    · intro firstPoint firstPointMember
        secondPoint secondPointMember equal
      simp at firstPointMember secondPointMember
      rcases firstPointMember with
        firstPointEq | firstPointEq
      · rcases secondPointMember with
          secondPointEq | secondPointEq
        · have contact :
              firstEntrance = secondEntrance := by
            calc
              firstEntrance = firstPoint := firstPointEq.symm
              _ = secondPoint := equal
              _ = secondEntrance := secondPointEq
          have endpoints :=
            contactsAtEndpoints
              (List.mem_of_mem_dropLast firstEntranceMember)
              (List.mem_of_mem_dropLast secondEntranceMember)
              contact
          have firstHead :
              first.head? = some firstEntrance :=
            route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
              firstNodup firstEntranceMember endpoints.1
          have secondHead :
              second.head? = some secondEntrance :=
            route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
              secondNodup secondEntranceMember endpoints.2
          have firstPrefixHead :
              first.dropLast.head? = some firstEntrance :=
            (dropLast_head?_eq_head?_of_ne_nil
              (route := first)
              (List.ne_nil_of_mem firstEntranceMember)).trans firstHead
          have secondPrefixHead :
              second.dropLast.head? = some secondEntrance :=
            (dropLast_head?_eq_head?_of_ne_nil
              (route := second)
              (List.ne_nil_of_mem secondEntranceMember)).trans secondHead
          apply notBothSingleton
          exact
            ⟨list_length_eq_one_of_nodup_of_head_last_eq
                firstPrefixNodup firstPrefixHead firstEntranceEq,
              list_length_eq_one_of_nodup_of_head_last_eq
                secondPrefixNodup secondPrefixHead secondEntranceEq⟩
        · have contact :
              firstEntrance = secondLast := by
            calc
              firstEntrance = firstPoint := firstPointEq.symm
              _ = secondPoint := equal
              _ = secondLast := secondPointEq
          have endpoints :=
            contactsAtEndpoints
              (List.mem_of_mem_dropLast firstEntranceMember)
              secondFinalEndpoints.2 contact
          have firstHead :
              first.head? = some firstEntrance :=
            route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
              firstNodup firstEntranceMember endpoints.1
          exact headLastNe
            (firstHead.trans
              ((congrArg some contact).trans secondLastEq.symm))
      · rcases secondPointMember with
          secondPointEq | secondPointEq
        · have contact :
              firstLast = secondEntrance := by
            calc
              firstLast = firstPoint := firstPointEq.symm
              _ = secondPoint := equal
              _ = secondEntrance := secondPointEq
          have endpoints :=
            contactsAtEndpoints firstFinalEndpoints.2
              (List.mem_of_mem_dropLast secondEntranceMember)
              contact
          have secondHead :
              second.head? = some secondEntrance :=
            route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
              secondNodup secondEntranceMember endpoints.2
          exact lastHeadNe
            (firstLastEq.trans
              ((congrArg some contact).trans secondHead.symm))
        · have contact :
              firstLast = secondLast := by
            calc
              firstLast = firstPoint := firstPointEq.symm
              _ = secondPoint := equal
              _ = secondLast := secondPointEq
          exact lastLastNe
            (firstLastEq.trans
              ((congrArg some contact).trans secondLastEq.symm))
  have separated :=
    finalSegment_coordinateRectanglesSeparated_of_strictlyAvoid
      (first := [firstEntrance, firstLast])
      (second := [secondEntrance, secondLast])
      (by simp) (by simp)
      (by
        simpa [polylineLastEntrance, polylineFirstExit,
          firstFinal] using firstAligned)
      (by
        simpa [polylineLastEntrance, polylineFirstExit,
          secondFinal] using secondAligned)
      finalRoutesStrict
  simpa [polylineLastEntrance, polylineFirstExit,
    firstFinal, secondFinal, List.getLastD_eq_getLast?] using separated

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

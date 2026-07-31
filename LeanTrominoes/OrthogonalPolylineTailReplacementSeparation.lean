import LeanTrominoes.RetainedRayPolylineTailReplacement
import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Strict separation under polyline tail replacement

Replacing the variable-side endpoint of two incidence routes decomposes
each new route into its old `dropLast` prefix and a replacement suffix.
This file supplies the compositional separation theorem for that operation.
After applying it, a geometric construction only needs to establish the
four prefix/suffix separation cases.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every segment of a route with its last point removed was already a
segment of the original route. -/
theorem gridPolylineSegments_dropLast_subset
    (points : List Cell) :
    ∀ ⦃segment⦄,
      segment ∈ gridPolylineSegments points.dropLast →
        segment ∈ gridPolylineSegments points := by
  intro segment member
  induction points using List.twoStepInduction with
  | nil =>
      simp [gridPolylineSegments] at member
  | singleton point =>
      simp [gridPolylineSegments] at member
  | cons_cons first second rest _ induction =>
      cases rest with
      | nil =>
          simp [gridPolylineSegments] at member
      | cons third rest =>
          simp only [List.dropLast_cons_cons,
            gridPolylineSegments, List.mem_cons] at member ⊢
          rcases member with rfl | member
          · exact Or.inl rfl
          · exact Or.inr (by
              simpa [gridPolylineSegments] using
                induction second member)

/-- Removing the last point of the first route preserves strict
separation. -/
theorem RoutesStrictlyAvoidEachOther.dropLast_left
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther first.dropLast second := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    exact strict.1 firstSegment
      (gridPolylineSegments_dropLast_subset first firstMember)
      secondSegment secondMember
  · intro firstPoint firstMember secondSegment secondMember
    exact strict.2.1 firstPoint
      (List.mem_of_mem_dropLast firstMember)
      secondSegment secondMember
  · intro secondPoint secondMember firstSegment firstMember
    exact strict.2.2.1 secondPoint secondMember
      firstSegment
      (gridPolylineSegments_dropLast_subset first firstMember)
  · intro firstPoint firstMember secondPoint secondMember
    exact strict.2.2.2 firstPoint
      (List.mem_of_mem_dropLast firstMember)
      secondPoint secondMember

/-- Removing the last point of the second route preserves strict
separation. -/
theorem RoutesStrictlyAvoidEachOther.dropLast_right
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther first second.dropLast :=
  strict.symm.dropLast_left.symm

/-- Ordinary continuous separation becomes strict after removing both final
points, provided no listed contact remains between the two prefixes. -/
theorem routesStrictlyAvoidEachOther_dropLast_of_avoid_of_noContact
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (noContact :
      ∀ firstPoint ∈ first.dropLast,
        ∀ secondPoint ∈ second.dropLast,
          firstPoint ≠ secondPoint) :
    RoutesStrictlyAvoidEachOther first.dropLast second.dropLast := by
  unfold RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, noContact⟩
  · intro firstSegment firstMember secondSegment secondMember
    have firstOriginal :=
      gridPolylineSegments_dropLast_subset first firstMember
    have secondOriginal :=
      gridPolylineSegments_dropLast_subset second secondMember
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondOriginal with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.1 firstIndex secondIndex
  · intro firstPoint firstMember secondSegment secondMember
    have firstOriginal := List.mem_of_mem_dropLast firstMember
    have secondOriginal :=
      gridPolylineSegments_dropLast_subset second secondMember
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondOriginal with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.2.1 firstIndex secondIndex
  · intro secondPoint secondMember firstSegment firstMember
    have secondOriginal := List.mem_of_mem_dropLast secondMember
    have firstOriginal :=
      gridPolylineSegments_dropLast_subset first firstMember
    rcases List.mem_iff_get.mp secondOriginal with
      ⟨secondIndex, secondEqual⟩
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rw [← secondEqual, ← firstEqual]
    exact avoid.2.2.1 secondIndex firstIndex

/-- In a duplicate-free list, its removed final point cannot still occur in
`dropLast`. -/
theorem getLast?_ne_some_of_mem_dropLast_of_nodup
    {α : Type*} {points : List α} {point : α}
    (nodup : points.Nodup)
    (member : point ∈ points.dropLast) :
    points.getLast? ≠ some point := by
  intro last
  have appendEq :
      points.dropLast ++ [point] = points :=
    List.dropLast_append_getLast? point last
  have appendedNodup :
      (points.dropLast ++ [point]).Nodup := by
    rw [appendEq]
    exact nodup
  have disjoint :
      List.Disjoint points.dropLast [point] :=
    List.disjoint_of_nodup_append appendedNodup
  exact disjoint member (by simp)

/-- A simple route's final point is completely clear of the prefix obtained
by deleting that point: it is neither a listed prefix point nor anywhere on
an axis-aligned prefix segment. -/
theorem routeIsSimple_dropLast_avoids_final_point
    {route : List Cell} {finalPoint : Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (finalPointEq : route.getLast? = some finalPoint) :
    (∀ point ∈ route.dropLast, point ≠ finalPoint) ∧
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains finalPoint := by
  have pointAvoid :
      ∀ point ∈ route.dropLast, point ≠ finalPoint := by
    intro point pointMember equal
    subst point
    exact
      (getLast?_ne_some_of_mem_dropLast_of_nodup
        simple.1 pointMember)
        finalPointEq
  refine ⟨pointAvoid, ?_⟩
  intro segment segmentMember _axisAligned contains
  have segmentOriginal :
      segment ∈ gridPolylineSegments route :=
    gridPolylineSegments_dropLast_subset route segmentMember
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        contains with
    interior | endpoint
  · exact
      (simple.2.1 finalPoint
        (mem_of_getLast?_eq_some finalPointEq)
        segment segmentOriginal)
        interior
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    rcases endpoint with atStart | atFinish
    · exact (pointAvoid segment.start endpoints.1) atStart.symm
    · exact (pointAvoid segment.finish endpoints.2) atFinish.symm

/-- If two routes meet only at advertised endpoints and the first route's
source differs from the second route's target, then deleting the first
target leaves a prefix completely clear of the second target. -/
theorem routePrefix_avoids_other_final_point_of_avoid
    {first second : List Cell}
    {firstSource secondFinal : Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (firstHead : first.head? = some firstSource)
    (secondLast : second.getLast? = some secondFinal)
    (sourceNeFinal : firstSource ≠ secondFinal) :
    (∀ point ∈ first.dropLast, point ≠ secondFinal) ∧
      ∀ segment ∈ gridPolylineSegments first.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains secondFinal := by
  have secondFinalMember : secondFinal ∈ second :=
    mem_of_getLast?_eq_some secondLast
  have pointAvoid :
      ∀ point ∈ first.dropLast, point ≠ secondFinal := by
    intro point pointMember equal
    have firstOriginal : point ∈ first :=
      List.mem_of_mem_dropLast pointMember
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondFinalMember with
      ⟨secondIndex, secondEqual⟩
    have indexedEqual :
        first.get firstIndex = second.get secondIndex :=
      firstEqual.trans (equal.trans secondEqual.symm)
    have firstEndpoint :=
      (avoid.2.2.2 firstIndex secondIndex indexedEqual).1
    rcases firstEndpoint with atHead | atLast
    · apply sourceNeFinal
      apply Option.some.inj
      rw [← firstHead, atHead, firstEqual, equal]
    · have firstLastEq :
          first.getLast? = some point := by
        rw [atLast, firstEqual]
      exact
        (getLast?_ne_some_of_mem_dropLast_of_nodup
          firstNodup pointMember)
          firstLastEq
  refine ⟨pointAvoid, ?_⟩
  intro segment segmentMember _axisAligned contains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        contains with
    interior | endpoint
  · have segmentOriginal :
        segment ∈ gridPolylineSegments first :=
      gridPolylineSegments_dropLast_subset first segmentMember
    rcases List.mem_iff_get.mp segmentOriginal with
      ⟨segmentIndex, segmentEqual⟩
    rcases List.mem_iff_get.mp secondFinalMember with
      ⟨secondIndex, secondEqual⟩
    have interiorAvoid :=
      avoid.2.2.1 secondIndex segmentIndex
    rw [segmentEqual, secondEqual] at interiorAvoid
    exact interiorAvoid interior
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    rcases endpoint with atStart | atFinish
    · exact (pointAvoid segment.start endpoints.1) atStart.symm
    · exact (pointAvoid segment.finish endpoints.2) atFinish.symm

/-- Complete route avoidance, strict prefix separation, and clearance from
the second final point together separate the first retained prefix from the
second route's discarded final segment. -/
theorem routesStrictlyAvoidEachOther_dropLast_finalSegment
    {first second : List Cell}
    {secondEntrance secondFinal : Cell}
    (avoid : RoutesAvoidEachOther first second)
    (prefixesAvoid :
      RoutesStrictlyAvoidEachOther
        first.dropLast second.dropLast)
    (secondEntranceEq :
      second.dropLast.getLast? = some secondEntrance)
    (secondFinalEq :
      second.getLast? = some secondFinal)
    (firstPointsAvoidFinal :
      ∀ point ∈ first.dropLast, point ≠ secondFinal) :
    RoutesStrictlyAvoidEachOther
      first.dropLast [secondEntrance, secondFinal] := by
  have secondDropNonempty : second.dropLast ≠ [] := by
    intro empty
    rw [empty] at secondEntranceEq
    simp at secondEntranceEq
  have secondDecomposition :
      second.dropLast ++ [secondFinal] = second :=
    List.dropLast_append_getLast?
      secondFinal secondFinalEq
  have secondEntranceLastD :
      second.dropLast.getLastD (0, 0) =
        secondEntrance := by
    rw [List.getLastD_eq_getLast?, secondEntranceEq]
    simp
  let finalSegment : GridSegment :=
    ⟨secondEntrance, secondFinal⟩
  have finalSegmentMember :
      finalSegment ∈ gridPolylineSegments second := by
    rw [← secondDecomposition,
      gridPolylineSegments_append_singleton_of_ne_nil
        second.dropLast (0, 0) secondFinal
        secondDropNonempty,
      List.mem_append]
    apply Or.inr
    simp only [List.mem_singleton]
    simpa [finalSegment] using secondEntranceLastD.symm
  have secondEntranceMember :
      secondEntrance ∈ second.dropLast :=
    mem_of_getLast?_eq_some secondEntranceEq
  have secondFinalMember :
      secondFinal ∈ second :=
    mem_of_getLast?_eq_some secondFinalEq
  unfold RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstSegmentMember
      terminalSegment terminalSegmentMember
    have firstOriginal :=
      gridPolylineSegments_dropLast_subset
        first firstSegmentMember
    have terminalSegmentEq :
        terminalSegment = finalSegment := by
      simpa [gridPolylineSegments, finalSegment] using
        terminalSegmentMember
    subst terminalSegment
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp finalSegmentMember with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.1 firstIndex secondIndex
  · intro firstPoint firstPointMember
      terminalSegment terminalSegmentMember
    have firstOriginal :=
      List.mem_of_mem_dropLast firstPointMember
    have terminalSegmentEq :
        terminalSegment = finalSegment := by
      simpa [gridPolylineSegments, finalSegment] using
        terminalSegmentMember
    subst terminalSegment
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp finalSegmentMember with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.2.1 firstIndex secondIndex
  · intro terminalPoint terminalPointMember
      firstSegment firstSegmentMember
    have firstOriginal :=
      gridPolylineSegments_dropLast_subset
        first firstSegmentMember
    rcases List.mem_iff_get.mp firstOriginal with
      ⟨firstIndex, firstEqual⟩
    have terminalPointOriginal :
        terminalPoint ∈ second := by
      simp at terminalPointMember
      rcases terminalPointMember with
          rfl | rfl
      · exact
          List.mem_of_mem_dropLast
            secondEntranceMember
      · exact secondFinalMember
    rcases List.mem_iff_get.mp terminalPointOriginal with
      ⟨secondIndex, secondEqual⟩
    rw [← secondEqual, ← firstEqual]
    exact avoid.2.2.1 secondIndex firstIndex
  · intro firstPoint firstPointMember
      terminalPoint terminalPointMember
    simp at terminalPointMember
    rcases terminalPointMember with rfl | rfl
    · exact
        prefixesAvoid.2.2.2
          firstPoint firstPointMember
          terminalPoint secondEntranceMember
    · exact
        firstPointsAvoidFinal
          firstPoint firstPointMember

/-- Endpoint-only contact leaves no contact between final-point-deleted
prefixes when both routes are simple and have different source endpoints. -/
theorem noContact_dropLast_of_avoid_of_nodup_of_heads_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup)
    (headsDifferent : first.head? ≠ second.head?) :
    ∀ firstPoint ∈ first.dropLast,
      ∀ secondPoint ∈ second.dropLast,
        firstPoint ≠ secondPoint := by
  intro firstPoint firstMember secondPoint secondMember equal
  have firstOriginal := List.mem_of_mem_dropLast firstMember
  have secondOriginal := List.mem_of_mem_dropLast secondMember
  rcases List.mem_iff_get.mp firstOriginal with
    ⟨firstIndex, firstEqual⟩
  rcases List.mem_iff_get.mp secondOriginal with
    ⟨secondIndex, secondEqual⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstEqual.trans (equal.trans secondEqual.symm)
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex indexedEqual
  rcases endpoints.1 with firstHead | firstLast
  · rcases endpoints.2 with secondHead | secondLast
    · apply headsDifferent
      rw [firstHead, secondHead, indexedEqual]
    · exact
        (getLast?_ne_some_of_mem_dropLast_of_nodup
          secondNodup secondMember)
          (by simpa [← secondEqual] using secondLast)
  · exact
      (getLast?_ne_some_of_mem_dropLast_of_nodup
        firstNodup firstMember)
        (by simpa [← firstEqual] using firstLast)

/-- The common retained-source situation: endpoint-clean, simple routes with
different clause endpoints have strictly separated prefixes after deleting
their shared variable endpoint. -/
theorem routesStrictlyAvoidEachOther_dropLast_of_avoid_of_nodup_of_heads_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup)
    (headsDifferent : first.head? ≠ second.head?) :
    RoutesStrictlyAvoidEachOther first.dropLast second.dropLast :=
  routesStrictlyAvoidEachOther_dropLast_of_avoid_of_noContact
    avoid
    (noContact_dropLast_of_avoid_of_nodup_of_heads_ne
      avoid firstNodup secondNodup headsDifferent)

/-- A listed point of a duplicate-free route that survives deletion of the
final point cannot be the original final endpoint.  If it is an advertised
endpoint at all, it is therefore the head. -/
theorem route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
    {route : List Cell} {point : Cell}
    (nodup : route.Nodup)
    (member : point ∈ route.dropLast)
    (endpoint : RoutePointIsEndpoint route point) :
    route.head? = some point := by
  rcases endpoint with atHead | atLast
  · exact atHead
  · exact
      (getLast?_ne_some_of_mem_dropLast_of_nodup
        nodup member atLast).elim

/-- A nonempty final-point-deleted prefix retains the original route's
head. -/
theorem dropLast_head?_eq_head?_of_ne_nil
    {route : List Cell}
    (prefixNonempty : route.dropLast ≠ []) :
    route.dropLast.head? = route.head? := by
  cases route with
  | nil =>
      simp at prefixNonempty
  | cons first rest =>
      cases rest with
      | nil =>
          simp at prefixNonempty
      | cons second tail =>
          simp

/-- Deleting the final point from two duplicate-free, endpoint-clean routes
preserves ordinary route avoidance.  A surviving listed contact can only be
the original head of each route, hence remains an advertised endpoint of
both prefixes. -/
theorem routesAvoidEachOther_dropLast_of_avoid_of_nodup
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup) :
    RoutesAvoidEachOther first.dropLast second.dropLast := by
  unfold RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    have firstMember :
        (gridPolylineSegments first.dropLast).get firstIndex ∈
          gridPolylineSegments first :=
      gridPolylineSegments_dropLast_subset first
        (List.get_mem _ firstIndex)
    have secondMember :
        (gridPolylineSegments second.dropLast).get secondIndex ∈
          gridPolylineSegments second :=
      gridPolylineSegments_dropLast_subset second
        (List.get_mem _ secondIndex)
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstOriginalIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondOriginalIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.1 firstOriginalIndex secondOriginalIndex
  · intro firstIndex secondIndex
    have firstMember :
        first.dropLast.get firstIndex ∈ first :=
      List.mem_of_mem_dropLast (List.get_mem _ firstIndex)
    have secondMember :
        (gridPolylineSegments second.dropLast).get secondIndex ∈
          gridPolylineSegments second :=
      gridPolylineSegments_dropLast_subset second
        (List.get_mem _ secondIndex)
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstOriginalIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondOriginalIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.2.1 firstOriginalIndex secondOriginalIndex
  · intro secondIndex firstIndex
    have secondMember :
        second.dropLast.get secondIndex ∈ second :=
      List.mem_of_mem_dropLast (List.get_mem _ secondIndex)
    have firstMember :
        (gridPolylineSegments first.dropLast).get firstIndex ∈
          gridPolylineSegments first :=
      gridPolylineSegments_dropLast_subset first
        (List.get_mem _ firstIndex)
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondOriginalIndex, secondEqual⟩
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstOriginalIndex, firstEqual⟩
    rw [← secondEqual, ← firstEqual]
    exact avoid.2.2.1 secondOriginalIndex firstOriginalIndex
  · intro firstIndex secondIndex equal
    have firstMember :
        first.dropLast.get firstIndex ∈ first.dropLast :=
      List.get_mem _ firstIndex
    have secondMember :
        second.dropLast.get secondIndex ∈ second.dropLast :=
      List.get_mem _ secondIndex
    have firstOriginalMember :
        first.dropLast.get firstIndex ∈ first :=
      List.mem_of_mem_dropLast firstMember
    have secondOriginalMember :
        second.dropLast.get secondIndex ∈ second :=
      List.mem_of_mem_dropLast secondMember
    rcases List.mem_iff_get.mp firstOriginalMember with
      ⟨firstOriginalIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondOriginalMember with
      ⟨secondOriginalIndex, secondEqual⟩
    have originalEqual :
        first.get firstOriginalIndex =
          second.get secondOriginalIndex := by
      rw [firstEqual, secondEqual]
      exact equal
    have originalEndpoints :=
      avoid.2.2.2 firstOriginalIndex secondOriginalIndex
        originalEqual
    rw [firstEqual, secondEqual] at originalEndpoints
    constructor
    · left
      exact
        (dropLast_head?_eq_head?_of_ne_nil
          (route := first)
          (List.ne_nil_of_mem firstMember)).trans
          (route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
            firstNodup firstMember originalEndpoints.1)
    · left
      exact
        (dropLast_head?_eq_head?_of_ne_nil
          (route := second)
          (List.ne_nil_of_mem secondMember)).trans
          (route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
            secondNodup secondMember originalEndpoints.2)

/-- Any contact between final-point-deleted prefixes of duplicate-free,
endpoint-clean routes occurs at the retained head of both prefixes. -/
theorem routePrefix_contactsAtHeads_of_avoid_of_nodup
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup) :
    ∀ firstPoint ∈ first.dropLast,
      ∀ secondPoint ∈ second.dropLast,
        firstPoint = secondPoint →
          first.dropLast.head? = some firstPoint ∧
            second.dropLast.head? = some secondPoint := by
  intro firstPoint firstMember secondPoint secondMember equal
  have firstOriginalMember :
      firstPoint ∈ first :=
    List.mem_of_mem_dropLast firstMember
  have secondOriginalMember :
      secondPoint ∈ second :=
    List.mem_of_mem_dropLast secondMember
  rcases List.mem_iff_get.mp firstOriginalMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondOriginalMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex := by
    rw [firstIndexed, secondIndexed]
    exact equal
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  exact
    ⟨(dropLast_head?_eq_head?_of_ne_nil
        (route := first)
        (List.ne_nil_of_mem firstMember)).trans
        (route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
          firstNodup firstMember endpoints.1),
      (dropLast_head?_eq_head?_of_ne_nil
        (route := second)
        (List.ne_nil_of_mem secondMember)).trans
        (route_head?_eq_some_of_mem_dropLast_of_nodup_of_endpoint
          secondNodup secondMember endpoints.2)⟩

/-- Membership-form introduction rule for ordinary route avoidance. -/
theorem routesAvoidEachOther_of_mem
    {first second : List Cell}
    (segmentsAvoid :
      ∀ firstSegment ∈ gridPolylineSegments first,
        ∀ secondSegment ∈ gridPolylineSegments second,
          ¬GridSegment.InteriorsMeet firstSegment secondSegment)
    (firstPointsAvoid :
      ∀ firstPoint ∈ first,
        ∀ secondSegment ∈ gridPolylineSegments second,
          ¬secondSegment.InteriorContains firstPoint)
    (secondPointsAvoid :
      ∀ secondPoint ∈ second,
        ∀ firstSegment ∈ gridPolylineSegments first,
          ¬firstSegment.InteriorContains secondPoint)
    (contactsAtEndpoints :
      ∀ firstPoint ∈ first,
        ∀ secondPoint ∈ second,
          firstPoint = secondPoint →
            RoutePointIsEndpoint first firstPoint ∧
              RoutePointIsEndpoint second secondPoint) :
    RoutesAvoidEachOther first second := by
  unfold RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    exact
      segmentsAvoid
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex)
  · intro firstIndex secondIndex
    exact
      firstPointsAvoid
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex)
  · intro secondIndex firstIndex
    exact
      secondPointsAvoid
        _ (List.get_mem _ secondIndex)
        _ (List.get_mem _ firstIndex)
  · intro firstIndex secondIndex equal
    exact
      contactsAtEndpoints
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex) equal

/-- Positive uniform scaling preserves ordinary endpoint-only route
avoidance. -/
theorem RoutesAvoidEachOther.scalePolyline
    {first second : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (avoid : RoutesAvoidEachOther first second) :
    RoutesAvoidEachOther
      (LeanTrominoes.scalePolyline factor first)
      (LeanTrominoes.scalePolyline factor second) := by
  apply routesAvoidEachOther_of_mem
  · rw [gridPolylineSegments_scalePolyline,
      gridPolylineSegments_scalePolyline]
    intro firstSegment firstMember secondSegment secondMember
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    rcases List.mem_iff_get.mp originalFirstMember with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp originalSecondMember with
      ⟨secondIndex, secondEqual⟩
    intro meet
    apply avoid.1 firstIndex secondIndex
    rw [firstEqual, secondEqual]
    exact
      (GridSegment.interiorsMeet_scale_iff
        factorPositive originalFirst originalSecond).mp meet
  · rw [gridPolylineSegments_scalePolyline]
    intro firstPoint firstMember secondSegment secondMember
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    rcases List.mem_iff_get.mp originalFirstMember with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp originalSecondMember with
      ⟨secondIndex, secondEqual⟩
    intro contains
    apply avoid.2.1 firstIndex secondIndex
    rw [firstEqual, secondEqual]
    exact
      (GridSegment.interiorContains_scale_iff
        factorPositive originalSecond originalFirst).mp contains
  · rw [gridPolylineSegments_scalePolyline]
    intro secondPoint secondMember firstSegment firstMember
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_iff_get.mp originalSecondMember with
      ⟨secondIndex, secondEqual⟩
    rcases List.mem_iff_get.mp originalFirstMember with
      ⟨firstIndex, firstEqual⟩
    intro contains
    apply avoid.2.2.1 secondIndex firstIndex
    rw [secondEqual, firstEqual]
    exact
      (GridSegment.interiorContains_scale_iff
        factorPositive originalFirst originalSecond).mp contains
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    rcases List.mem_iff_get.mp originalFirstMember with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp originalSecondMember with
      ⟨secondIndex, secondEqual⟩
    have originalEqual :
        originalFirst = originalSecond :=
      Cell.scale_injective factorPositive.ne' equal
    have endpoints :=
      avoid.2.2.2 firstIndex secondIndex
        (firstEqual.trans
          (originalEqual.trans secondEqual.symm))
    rw [firstEqual, secondEqual] at endpoints
    constructor
    · rcases endpoints.1 with atHead | atLast
      · left
        simpa using
          congrArg (Option.map (Cell.scale factor)) atHead
      · right
        simpa using
          congrArg (Option.map (Cell.scale factor)) atLast
    · rcases endpoints.2 with atHead | atLast
      · left
        simpa using
          congrArg (Option.map (Cell.scale factor)) atHead
      · right
        simpa using
          congrArg (Option.map (Cell.scale factor)) atLast

/-- Join two replacement tails onto an ordinarily separated pair of
prefixes.  All contacts inherited from the prefixes must be at their heads;
the three pairs involving a replacement are contact-free. -/
theorem RoutesAvoidEachOther.join_tails_of_prefixes
    {first second firstReplacement secondReplacement : List Cell}
    {firstMiddle secondMiddle : Cell}
    (prefixesAvoid : RoutesAvoidEachOther first second)
    (prefixContactsAtHeads :
      ∀ firstPoint ∈ first,
        ∀ secondPoint ∈ second,
          firstPoint = secondPoint →
            first.head? = some firstPoint ∧
              second.head? = some secondPoint)
    (firstPrefixAvoidSecondReplacement :
      RoutesStrictlyAvoidEachOther
        first secondReplacement)
    (firstReplacementAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        firstReplacement second)
    (replacementsAvoid :
      RoutesStrictlyAvoidEachOther
        firstReplacement secondReplacement)
    (firstEntrance :
      first.getLast? = some firstMiddle)
    (firstReplacementHead :
      firstReplacement.head? = some firstMiddle)
    (secondEntrance :
      second.getLast? = some secondMiddle)
    (secondReplacementHead :
      secondReplacement.head? = some secondMiddle) :
    RoutesAvoidEachOther
      (joinAtEndpoint first firstReplacement)
      (joinAtEndpoint second secondReplacement) := by
  have firstSegments :=
    gridPolylineSegments_joinAtEndpoint
      firstEntrance firstReplacementHead
  have secondSegments :=
    gridPolylineSegments_joinAtEndpoint
      secondEntrance secondReplacementHead
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstMember secondSegment secondMember
    rw [firstSegments, List.mem_append] at firstMember
    rw [secondSegments, List.mem_append] at secondMember
    rcases firstMember with
        firstPrefixMember | firstReplacementMember <;>
      rcases secondMember with
        secondPrefixMember | secondReplacementMember
    · rcases List.mem_iff_get.mp firstPrefixMember with
        ⟨firstPrefixIndex, firstEqual⟩
      rcases List.mem_iff_get.mp secondPrefixMember with
        ⟨secondPrefixIndex, secondEqual⟩
      rw [← firstEqual, ← secondEqual]
      exact prefixesAvoid.1 firstPrefixIndex secondPrefixIndex
    · exact
        firstPrefixAvoidSecondReplacement.1
          _ firstPrefixMember _ secondReplacementMember
    · exact
        firstReplacementAvoidSecondPrefix.1
          _ firstReplacementMember _ secondPrefixMember
    · exact
        replacementsAvoid.1
          _ firstReplacementMember _ secondReplacementMember
  · intro firstPoint firstMember secondSegment secondMember
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstReplacementMember <;>
      rw [secondSegments, List.mem_append] at secondMember <;>
    rcases secondMember with
        secondPrefixMember | secondReplacementMember
    · rcases List.mem_iff_get.mp firstPrefixMember with
        ⟨firstPrefixIndex, firstEqual⟩
      rcases List.mem_iff_get.mp secondPrefixMember with
        ⟨secondPrefixIndex, secondEqual⟩
      rw [← firstEqual, ← secondEqual]
      exact prefixesAvoid.2.1 firstPrefixIndex secondPrefixIndex
    · exact
        firstPrefixAvoidSecondReplacement.2.1
          _ firstPrefixMember _ secondReplacementMember
    · exact
        firstReplacementAvoidSecondPrefix.2.1
          _ firstReplacementMember _ secondPrefixMember
    · exact
        replacementsAvoid.2.1
          _ firstReplacementMember _ secondReplacementMember
  · intro secondPoint secondMember firstSegment firstMember
    rcases mem_joinAtEndpoint secondMember with
        secondPrefixMember | secondReplacementMember <;>
      rw [firstSegments, List.mem_append] at firstMember <;>
    rcases firstMember with
        firstPrefixMember | firstReplacementMember
    · rcases List.mem_iff_get.mp secondPrefixMember with
        ⟨secondPrefixIndex, secondEqual⟩
      rcases List.mem_iff_get.mp firstPrefixMember with
        ⟨firstPrefixIndex, firstEqual⟩
      rw [← secondEqual, ← firstEqual]
      exact prefixesAvoid.2.2.1 secondPrefixIndex firstPrefixIndex
    · exact
        firstReplacementAvoidSecondPrefix.2.2.1
          _ secondPrefixMember _ firstReplacementMember
    · exact
        firstPrefixAvoidSecondReplacement.2.2.1
          _ secondReplacementMember _ firstPrefixMember
    · exact
        replacementsAvoid.2.2.1
          _ secondReplacementMember _ firstReplacementMember
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstReplacementMember
    · rcases mem_joinAtEndpoint secondMember with
        secondPrefixMember | secondReplacementMember
      · have heads :=
          prefixContactsAtHeads
            _ firstPrefixMember _ secondPrefixMember equal
        exact
          ⟨Or.inl
              (joinAtEndpoint_head? heads.1),
            Or.inl
              (joinAtEndpoint_head? heads.2)⟩
      · exact
          (firstPrefixAvoidSecondReplacement.2.2.2
            _ firstPrefixMember _ secondReplacementMember equal).elim
    · rcases mem_joinAtEndpoint secondMember with
        secondPrefixMember | secondReplacementMember
      · exact
          (firstReplacementAvoidSecondPrefix.2.2.2
            _ firstReplacementMember _ secondPrefixMember equal).elim
      · exact
          (replacementsAvoid.2.2.2
            _ firstReplacementMember _ secondReplacementMember equal).elim

/-- Simultaneous tail replacement preserves strict separation once all four
prefix/suffix pairs are strictly separated. -/
theorem RoutesStrictlyAvoidEachOther.replace_tails_of_prefixes
    {first second firstReplacement secondReplacement : List Cell}
    {firstMiddle secondMiddle : Cell}
    (prefixesAvoid :
      RoutesStrictlyAvoidEachOther
        first.dropLast second.dropLast)
    (firstPrefixAvoidSecondReplacement :
      RoutesStrictlyAvoidEachOther
        first.dropLast secondReplacement)
    (firstReplacementAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        firstReplacement second.dropLast)
    (replacementsAvoid :
      RoutesStrictlyAvoidEachOther
        firstReplacement secondReplacement)
    (firstEntrance :
      first.dropLast.getLast? = some firstMiddle)
    (firstReplacementHead :
      firstReplacement.head? = some firstMiddle)
    (secondEntrance :
      second.dropLast.getLast? = some secondMiddle)
    (secondReplacementHead :
      secondReplacement.head? = some secondMiddle) :
    RoutesStrictlyAvoidEachOther
    (replacePolylineTail first firstReplacement)
      (replacePolylineTail second secondReplacement) := by
  rw [PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      first firstReplacement firstEntrance firstReplacementHead,
    PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      second secondReplacement secondEntrance secondReplacementHead]
  have joinedAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint first.dropLast firstReplacement)
        second.dropLast :=
    prefixesAvoid.join_left
      firstReplacementAvoidSecondPrefix
      firstEntrance firstReplacementHead
  have joinedAvoidSecondReplacement :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint first.dropLast firstReplacement)
        secondReplacement :=
    firstPrefixAvoidSecondReplacement.join_left
      replacementsAvoid
      firstEntrance firstReplacementHead
  exact joinedAvoidSecondPrefix.join_right
    joinedAvoidSecondReplacement
    secondEntrance secondReplacementHead

/-- Simultaneous tail replacement preserves strict separation once the
four prefix/suffix pairs are strictly separated.

The original-route hypothesis supplies prefix/prefix separation
automatically.  The other three hypotheses are the genuinely new geometric
obligations introduced by the replacement suffixes. -/
theorem RoutesStrictlyAvoidEachOther.replace_tails
    {first second firstReplacement secondReplacement : List Cell}
    {firstMiddle secondMiddle : Cell}
    (originalAvoid :
      RoutesStrictlyAvoidEachOther first second)
    (firstPrefixAvoidSecondReplacement :
      RoutesStrictlyAvoidEachOther
        first.dropLast secondReplacement)
    (firstReplacementAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        firstReplacement second.dropLast)
    (replacementsAvoid :
      RoutesStrictlyAvoidEachOther
        firstReplacement secondReplacement)
    (firstEntrance :
      first.dropLast.getLast? = some firstMiddle)
    (firstReplacementHead :
      firstReplacement.head? = some firstMiddle)
    (secondEntrance :
      second.dropLast.getLast? = some secondMiddle)
    (secondReplacementHead :
      secondReplacement.head? = some secondMiddle) :
    RoutesStrictlyAvoidEachOther
      (replacePolylineTail first firstReplacement)
      (replacePolylineTail second secondReplacement) :=
  RoutesStrictlyAvoidEachOther.replace_tails_of_prefixes
    (originalAvoid.dropLast_left.dropLast_right)
    firstPrefixAvoidSecondReplacement
    firstReplacementAvoidSecondPrefix replacementsAvoid
    firstEntrance firstReplacementHead
    secondEntrance secondReplacementHead

/-- Simultaneous tail replacement preserves ordinary endpoint-only
avoidance for duplicate-free original routes.  This is the common-clause
counterpart of strict tail-replacement separation: a shared clause head is
retained as the sole permitted contact, while every pair involving a new
replacement suffix is contact-free. -/
theorem RoutesAvoidEachOther.replace_tails
    {first second firstReplacement secondReplacement : List Cell}
    {firstMiddle secondMiddle : Cell}
    (originalAvoid :
      RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup)
    (firstPrefixAvoidSecondReplacement :
      RoutesStrictlyAvoidEachOther
        first.dropLast secondReplacement)
    (firstReplacementAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        firstReplacement second.dropLast)
    (replacementsAvoid :
      RoutesStrictlyAvoidEachOther
        firstReplacement secondReplacement)
    (firstEntrance :
      first.dropLast.getLast? = some firstMiddle)
    (firstReplacementHead :
      firstReplacement.head? = some firstMiddle)
    (secondEntrance :
      second.dropLast.getLast? = some secondMiddle)
    (secondReplacementHead :
      secondReplacement.head? = some secondMiddle) :
    RoutesAvoidEachOther
      (replacePolylineTail first firstReplacement)
      (replacePolylineTail second secondReplacement) := by
  rw [PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      first firstReplacement firstEntrance firstReplacementHead,
    PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      second secondReplacement secondEntrance secondReplacementHead]
  exact
    RoutesAvoidEachOther.join_tails_of_prefixes
      (routesAvoidEachOther_dropLast_of_avoid_of_nodup
        originalAvoid firstNodup secondNodup)
      (routePrefix_contactsAtHeads_of_avoid_of_nodup
        originalAvoid firstNodup secondNodup)
      firstPrefixAvoidSecondReplacement
      firstReplacementAvoidSecondPrefix
      replacementsAvoid
      firstEntrance firstReplacementHead
      secondEntrance secondReplacementHead

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes

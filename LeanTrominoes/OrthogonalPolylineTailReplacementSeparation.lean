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

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes

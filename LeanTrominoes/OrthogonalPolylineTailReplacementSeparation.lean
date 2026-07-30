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

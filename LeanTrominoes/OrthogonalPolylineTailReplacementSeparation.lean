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
      (replacePolylineTail second secondReplacement) := by
  rw [PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      first firstReplacement firstEntrance firstReplacementHead,
    PeriodicEightOccurrenceSplit.replacePolylineTail_eq_joinAtEndpoint_dropLast
      second secondReplacement secondEntrance secondReplacementHead]
  have joinedAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint first.dropLast firstReplacement)
        second.dropLast :=
    (originalAvoid.dropLast_left.dropLast_right).join_left
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

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes

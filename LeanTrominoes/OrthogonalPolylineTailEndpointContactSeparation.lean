import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineRouteReversalContacts
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Joining a tail-contacting route piece

An incidence route may legally end on an endpoint of another route.  When
the incidence route is assembled from a contact-free prefix and a final
piece, ordinary endpoint-only separation is preserved exactly when every
listed contact of the final piece occurs at its tail.

This module records that asymmetric contact condition, transports it
through injective point maps, and supplies the corresponding endpoint-join
lemma.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every listed contact occurs at the tail of the first route and at one
of the advertised endpoints of the second route. -/
def RoutesMeetOnlyAtFirstTail
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondPoint ∈ second,
      firstPoint = secondPoint →
        first.getLast? = some firstPoint ∧
          RoutePointIsEndpoint second secondPoint

instance (first second : List Cell) :
    Decidable (RoutesMeetOnlyAtFirstTail first second) := by
  unfold RoutesMeetOnlyAtFirstTail
  infer_instance

/-- Every listed contact occurs at the tail of both routes. -/
def RoutesMeetOnlyAtTails
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondPoint ∈ second,
      firstPoint = secondPoint →
        first.getLast? = some firstPoint ∧
          second.getLast? = some secondPoint

instance (first second : List Cell) :
    Decidable (RoutesMeetOnlyAtTails first second) := by
  unfold RoutesMeetOnlyAtTails
  infer_instance

/-- Tail-only listed contact is symmetric. -/
theorem RoutesMeetOnlyAtTails.symm
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtTails first second) :
    RoutesMeetOnlyAtTails second first := by
  intro secondPoint secondMember firstPoint firstMember equal
  have tails :=
    contacts firstPoint firstMember
      secondPoint secondMember equal.symm
  exact ⟨tails.2, tails.1⟩

/-- Deleting the obsolete head from two duplicate-free separated routes
preserves ordinary route avoidance. -/
theorem routesAvoidEachOther_tail_of_avoid_of_nodup
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup) :
    RoutesAvoidEachOther first.tail second.tail := by
  have reversedAvoid := routesAvoidEachOther_reverse avoid
  have dropped :=
    routesAvoidEachOther_dropLast_of_avoid_of_nodup
      reversedAvoid
      (List.nodup_reverse.mpr firstNodup)
      (List.nodup_reverse.mpr secondNodup)
  have restored := routesAvoidEachOther_reverse dropped
  simpa using restored

/-- After deleting duplicate-free source heads, every surviving listed
contact lies at the original final endpoint of both routes. -/
theorem routesMeetOnlyAtTails_tail_of_avoid_of_nodup
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup) :
    RoutesMeetOnlyAtTails first.tail second.tail := by
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  have firstOriginalMember : firstPoint ∈ first :=
    List.mem_of_mem_tail firstMember
  have secondOriginalMember : secondPoint ∈ second :=
    List.mem_of_mem_tail secondMember
  rcases List.mem_iff_get.mp firstOriginalMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondOriginalMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstIndexed.trans
      (pointsEqual.trans secondIndexed.symm)
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  have firstNotHead : first.head? ≠ some firstPoint := by
    intro firstHead
    rcases first with _ | ⟨head, tail⟩
    · simp at firstMember
    · simp only [List.tail_cons, List.head?_cons] at firstMember firstHead
      have headEqual : head = firstPoint := Option.some.inj firstHead
      exact (List.nodup_cons.mp firstNodup).1 (headEqual ▸ firstMember)
  have secondNotHead : second.head? ≠ some secondPoint := by
    intro secondHead
    rcases second with _ | ⟨head, tail⟩
    · simp at secondMember
    · simp only [List.tail_cons, List.head?_cons] at secondMember secondHead
      have headEqual : head = secondPoint := Option.some.inj secondHead
      exact (List.nodup_cons.mp secondNodup).1 (headEqual ▸ secondMember)
  have firstLast : first.getLast? = some firstPoint :=
    endpoints.1.resolve_left firstNotHead
  have secondLast : second.getLast? = some secondPoint :=
    endpoints.2.resolve_left secondNotHead
  have firstTailHead : ∃ point, first.tail.head? = some point := by
    have nonempty : first.tail ≠ [] := List.ne_nil_of_mem firstMember
    rcases tailEq : first.tail with _ | ⟨point, rest⟩
    · exact (nonempty tailEq).elim
    · exact ⟨point, rfl⟩
  have secondTailHead : ∃ point, second.tail.head? = some point := by
    have nonempty : second.tail ≠ [] := List.ne_nil_of_mem secondMember
    rcases tailEq : second.tail with _ | ⟨point, rest⟩
    · exact (nonempty tailEq).elim
    · exact ⟨point, rfl⟩
  rcases firstTailHead with ⟨firstHead, firstTailHead⟩
  rcases secondTailHead with ⟨secondHead, secondTailHead⟩
  exact
    ⟨List.getLast?_tail_eq_getLast? firstTailHead firstLast,
      List.getLast?_tail_eq_getLast? secondTailHead secondLast⟩

/-- Ordinary route separation has tail-only listed contact when the other
three endpoint pairings are unequal. -/
theorem RoutesAvoidEachOther.meetOnlyAtTails_of_endpoints_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (headHeadNe : first.head? ≠ second.head?)
    (headLastNe : first.head? ≠ second.getLast?)
    (lastHeadNe : first.getLast? ≠ second.head?) :
    RoutesMeetOnlyAtTails first second := by
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstIndexed.trans
      (pointsEqual.trans secondIndexed.symm)
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  rcases endpoints.1 with firstHead | firstLast <;>
    rcases endpoints.2 with secondHead | secondLast
  · exact
      (headHeadNe
        (firstHead.trans
          ((congrArg some pointsEqual).trans secondHead.symm))).elim
  · exact
      (headLastNe
        (firstHead.trans
          ((congrArg some pointsEqual).trans secondLast.symm))).elim
  · exact
      (lastHeadNe
        (firstLast.trans
          ((congrArg some pointsEqual).trans secondHead.symm))).elim
  · exact ⟨firstLast, secondLast⟩

/-- An injective point map preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.mapPoints
    {transform : Cell → Cell}
    (injective : Function.Injective transform)
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtFirstTail first second) :
    RoutesMeetOnlyAtFirstTail
      (first.map transform) (second.map transform) := by
  intro mappedFirst mappedFirstMember
    mappedSecond mappedSecondMember mappedEqual
  rcases List.mem_map.mp mappedFirstMember with
    ⟨firstPoint, firstMember, rfl⟩
  rcases List.mem_map.mp mappedSecondMember with
    ⟨secondPoint, secondMember, rfl⟩
  have pointsEqual : firstPoint = secondPoint :=
    injective mappedEqual
  have base :=
    contacts firstPoint firstMember
      secondPoint secondMember pointsEqual
  constructor
  · simpa using
      congrArg (Option.map transform) base.1
  · rcases base.2 with atHead | atLast
    · left
      simpa using
        congrArg (Option.map transform) atHead
    · right
      simpa using
        congrArg (Option.map transform) atLast

/-- A common translation preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.translate
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtFirstTail first second)
    (offset : Cell) :
    RoutesMeetOnlyAtFirstTail
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) :=
  contacts.mapPoints (cell_add_left_injective offset)

/-- Positive uniform scaling preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.scalePolyline
    {first second : List Cell}
    {factor : Int}
    (factorPositive : 0 < factor)
    (contacts : RoutesMeetOnlyAtFirstTail first second) :
    RoutesMeetOnlyAtFirstTail
      (LeanTrominoes.scalePolyline factor first)
      (LeanTrominoes.scalePolyline factor second) :=
  contacts.mapPoints (Cell.scale_injective factorPositive.ne')

/-- An injective point map preserves contacts that occur only at the two
route tails. -/
theorem RoutesMeetOnlyAtTails.mapPoints
    {transform : Cell → Cell}
    (injective : Function.Injective transform)
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtTails first second) :
    RoutesMeetOnlyAtTails
      (first.map transform) (second.map transform) := by
  intro mappedFirst mappedFirstMember
    mappedSecond mappedSecondMember mappedEqual
  rcases List.mem_map.mp mappedFirstMember with
    ⟨firstPoint, firstMember, rfl⟩
  rcases List.mem_map.mp mappedSecondMember with
    ⟨secondPoint, secondMember, rfl⟩
  have pointsEqual : firstPoint = secondPoint :=
    injective mappedEqual
  have tails :=
    contacts firstPoint firstMember
      secondPoint secondMember pointsEqual
  exact
    ⟨by simpa using congrArg (Option.map transform) tails.1,
      by simpa using congrArg (Option.map transform) tails.2⟩

/-- A common translation preserves contacts that occur only at the two
route tails. -/
theorem RoutesMeetOnlyAtTails.translate
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtTails first second)
    (offset : Cell) :
    RoutesMeetOnlyAtTails
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) :=
  contacts.mapPoints (cell_add_left_injective offset)

/-- Positive uniform scaling preserves contacts that occur only at the two
route tails. -/
theorem RoutesMeetOnlyAtTails.scalePolyline
    {first second : List Cell}
    {factor : Int}
    (factorPositive : 0 < factor)
    (contacts : RoutesMeetOnlyAtTails first second) :
    RoutesMeetOnlyAtTails
      (LeanTrominoes.scalePolyline factor first)
      (LeanTrominoes.scalePolyline factor second) :=
  contacts.mapPoints (Cell.scale_injective factorPositive.ne')

/-- Join two locally head-separated prefixes to two suffixes whose only
possible listed contact is at their final tails.  Strict cross separation
ensures that the two splice boundaries cannot become new contacts. -/
theorem RoutesAvoidEachOther.join_tails_of_prefix_heads_and_suffix_tails
    {first second firstSuffix secondSuffix : List Cell}
    {firstMiddle secondMiddle : Cell}
    (prefixesAvoid : RoutesAvoidEachOther first second)
    (prefixContactsAtHeads : RoutesMeetOnlyAtHeads first second)
    (firstPrefixAvoidSecondSuffix :
      RoutesStrictlyAvoidEachOther first secondSuffix)
    (firstSuffixAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther firstSuffix second)
    (suffixesAvoid :
      RoutesAvoidEachOther firstSuffix secondSuffix)
    (suffixContactsAtTails :
      RoutesMeetOnlyAtTails firstSuffix secondSuffix)
    (firstEntrance : first.getLast? = some firstMiddle)
    (firstSuffixHead : firstSuffix.head? = some firstMiddle)
    (secondEntrance : second.getLast? = some secondMiddle)
    (secondSuffixHead : secondSuffix.head? = some secondMiddle) :
    RoutesAvoidEachOther
      (joinAtEndpoint first firstSuffix)
      (joinAtEndpoint second secondSuffix) := by
  have firstSegments :=
    gridPolylineSegments_joinAtEndpoint
      firstEntrance firstSuffixHead
  have secondSegments :=
    gridPolylineSegments_joinAtEndpoint
      secondEntrance secondSuffixHead
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstMember secondSegment secondMember
    rw [firstSegments, List.mem_append] at firstMember
    rw [secondSegments, List.mem_append] at secondMember
    rcases firstMember with firstPrefixMember | firstSuffixMember <;>
      rcases secondMember with secondPrefixMember | secondSuffixMember
    · exact prefixesAvoid.segmentsAvoid_of_mem
        _ firstPrefixMember _ secondPrefixMember
    · exact firstPrefixAvoidSecondSuffix.1
        _ firstPrefixMember _ secondSuffixMember
    · exact firstSuffixAvoidSecondPrefix.1
        _ firstSuffixMember _ secondPrefixMember
    · exact suffixesAvoid.segmentsAvoid_of_mem
        _ firstSuffixMember _ secondSuffixMember
  · intro firstPoint firstMember secondSegment secondMember
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstSuffixMember <;>
      rw [secondSegments, List.mem_append] at secondMember <;>
      rcases secondMember with secondPrefixMember | secondSuffixMember
    · exact prefixesAvoid.firstPointsAvoid_of_mem
        _ firstPrefixMember _ secondPrefixMember
    · exact firstPrefixAvoidSecondSuffix.2.1
        _ firstPrefixMember _ secondSuffixMember
    · exact firstSuffixAvoidSecondPrefix.2.1
        _ firstSuffixMember _ secondPrefixMember
    · exact suffixesAvoid.firstPointsAvoid_of_mem
        _ firstSuffixMember _ secondSuffixMember
  · intro secondPoint secondMember firstSegment firstMember
    rcases mem_joinAtEndpoint secondMember with
        secondPrefixMember | secondSuffixMember <;>
      rw [firstSegments, List.mem_append] at firstMember <;>
      rcases firstMember with firstPrefixMember | firstSuffixMember
    · exact prefixesAvoid.secondPointsAvoid_of_mem
        _ secondPrefixMember _ firstPrefixMember
    · exact firstSuffixAvoidSecondPrefix.2.2.1
        _ secondPrefixMember _ firstSuffixMember
    · exact firstPrefixAvoidSecondSuffix.2.2.1
        _ secondSuffixMember _ firstPrefixMember
    · exact suffixesAvoid.secondPointsAvoid_of_mem
        _ secondSuffixMember _ firstSuffixMember
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstSuffixMember
    · rcases mem_joinAtEndpoint secondMember with
          secondPrefixMember | secondSuffixMember
      · have heads :=
          prefixContactsAtHeads
            _ firstPrefixMember _ secondPrefixMember equal
        exact
          ⟨Or.inl (joinAtEndpoint_head? heads.1),
            Or.inl (joinAtEndpoint_head? heads.2)⟩
      · exact
          (firstPrefixAvoidSecondSuffix.2.2.2
            _ firstPrefixMember _ secondSuffixMember equal).elim
    · rcases mem_joinAtEndpoint secondMember with
          secondPrefixMember | secondSuffixMember
      · exact
          (firstSuffixAvoidSecondPrefix.2.2.2
            _ firstSuffixMember _ secondPrefixMember equal).elim
      · have tails :=
          suffixContactsAtTails
            _ firstSuffixMember _ secondSuffixMember equal
        exact
          ⟨Or.inr
              (joinAtEndpoint_getLast?
                firstEntrance firstSuffixHead tails.1),
            Or.inr
              (joinAtEndpoint_getLast?
                secondEntrance secondSuffixHead tails.2)⟩

/-- Joining a contact-free prefix to an ordinarily separated final piece
preserves ordinary separation when every legal contact of the final piece
is at its tail. -/
theorem RoutesAvoidEachOther.join_left_of_tail_contact
    {first extra second : List Cell}
    {boundary : Cell}
    (firstAvoid :
      RoutesStrictlyAvoidEachOther first second)
    (extraAvoid :
      RoutesAvoidEachOther extra second)
    (extraContactsAtTail :
      RoutesMeetOnlyAtFirstTail extra second)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesAvoidEachOther
      (joinAtEndpoint first extra) second := by
  have joinedSegments :
      gridPolylineSegments (joinAtEndpoint first extra) =
        gridPolylineSegments first ++
          gridPolylineSegments extra :=
    gridPolylineSegments_joinAtEndpoint firstLast extraHead
  apply routesAvoidEachOther_of_mem
  · intro joinedSegment joinedMember
      secondSegment secondMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.1 joinedSegment firstMember
          secondSegment secondMember
    · exact
        extraAvoid.segmentsAvoid_of_mem
          joinedSegment extraMember
          secondSegment secondMember
  · intro joinedPoint joinedMember
      secondSegment secondMember
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        firstAvoid.2.1 joinedPoint firstMember
          secondSegment secondMember
    · exact
        extraAvoid.firstPointsAvoid_of_mem
          joinedPoint extraMember
          secondSegment secondMember
  · intro secondPoint secondMember
      joinedSegment joinedMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.2.2.1 secondPoint secondMember
          joinedSegment firstMember
    · exact
        extraAvoid.secondPointsAvoid_of_mem
          secondPoint secondMember
          joinedSegment extraMember
  · intro joinedPoint joinedMember
      secondPoint secondMember pointsEqual
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        (firstAvoid.2.2.2
          joinedPoint firstMember
          secondPoint secondMember pointsEqual).elim
    · have contacts :=
        extraContactsAtTail
          joinedPoint extraMember
          secondPoint secondMember pointsEqual
      have joinedLast :
          (joinAtEndpoint first extra).getLast? =
            some joinedPoint :=
        joinAtEndpoint_getLast?
          firstLast extraHead contacts.1
      exact ⟨Or.inr joinedLast, contacts.2⟩

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes

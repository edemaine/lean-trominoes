/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.OrthogonalPolylineMiddleCoarsening

/-!
# Unit subdivision of endpoint joins

Ordered unit subdivision commutes with joining two nondegenerate polylines at
a common endpoint.  This lets endpoint-isolation arguments reason separately
about a long prefix and a terminal suffix.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- Unit subdivision commutes with a correctly matched endpoint join when
the first route is nonempty. -/
theorem unitSubdividePolyline_joinAtEndpoint
    {first second : List Cell} {middle : Cell}
    (firstNonempty : first ≠ [])
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle) :
    unitSubdividePolyline (joinAtEndpoint first second) =
      joinAtEndpoint (unitSubdividePolyline first)
        (unitSubdividePolyline second) := by
  induction first using List.twoStepInduction with
  | nil => exact (firstNonempty rfl).elim
  | singleton point =>
      have pointEqual : point = middle := by
        simpa using firstLast
      subst point
      cases second with
      | nil => simp at secondHead
      | cons secondFirst secondRest =>
          have secondFirstEqual : secondFirst = middle := by
            simpa using secondHead
          subst secondFirst
          simp only [unitSubdividePolyline_singleton,
            joinAtEndpoint, List.tail_cons]
          apply Eq.symm
          apply List.cons_head?_tail
          rw [unitSubdividePolyline_head? (by simp)]
          simp
  | cons_cons first secondPoint rest _ tailInduction =>
      cases rest with
      | nil =>
          have secondPointEqual : secondPoint = middle := by
            simpa using firstLast
          subst secondPoint
          cases second with
          | nil => simp at secondHead
          | cons secondFirst secondRest =>
              have secondFirstEqual : secondFirst = middle := by
                simpa using secondHead
              subst secondFirst
              simp [unitSubdividePolyline, joinAtEndpoint]
      | cons third rest =>
          have tailLast :
              (secondPoint :: third :: rest).getLast? =
                some middle := by
            simpa using firstLast
          have tailEquality :=
            tailInduction secondPoint (by simp) tailLast
          calc
            unitSubdividePolyline
                (joinAtEndpoint
                  (first :: secondPoint :: third :: rest) second) =
              joinAtEndpoint (unitSegmentPoints first secondPoint)
                (unitSubdividePolyline
                  (joinAtEndpoint
                    (secondPoint :: third :: rest) second)) := by
                rw [show
                  joinAtEndpoint
                      (first :: secondPoint :: third :: rest) second =
                    first ::
                      joinAtEndpoint
                        (secondPoint :: third :: rest) second by
                  simp [joinAtEndpoint]]
                change
                  unitSubdividePolyline
                      (first :: secondPoint ::
                        (third :: rest ++ second.tail)) = _
                rw [unitSubdividePolyline]
                simp [joinAtEndpoint]
            _ =
              joinAtEndpoint (unitSegmentPoints first secondPoint)
                (joinAtEndpoint
                  (unitSubdividePolyline
                    (secondPoint :: third :: rest))
                  (unitSubdividePolyline second)) := by
                rw [tailEquality]
            _ =
              joinAtEndpoint
                (joinAtEndpoint (unitSegmentPoints first secondPoint)
                  (unitSubdividePolyline
                    (secondPoint :: third :: rest)))
                (unitSubdividePolyline second) :=
              joinAtEndpoint_assoc_of_middle_ne_nil
                (unitSubdividePolyline_ne_nil (by simp))
            _ =
              joinAtEndpoint
                (unitSubdividePolyline
                  (first :: secondPoint :: third :: rest))
                (unitSubdividePolyline second) := by
              rw [show
                unitSubdividePolyline
                    (first :: secondPoint :: third :: rest) =
                  joinAtEndpoint (unitSegmentPoints first secondPoint)
                    (unitSubdividePolyline
                      (secondPoint :: third :: rest)) by
                simp only [unitSubdividePolyline]]

/-- Joining a suffix to a prefix with an isolated first point preserves
first-point isolation when that point is absent from the suffix tail. -/
theorem HeadNotInTail.joinAtEndpoint
    {first second : List Cell} {head : Cell}
    (fresh : HeadNotInTail first)
    (firstHead : first.head? = some head)
    (headNotInSecondTail : head ∉ second.tail) :
    HeadNotInTail (LeanTrominoes.joinAtEndpoint first second) := by
  intro joinedHead joinedHeadLookup joinedHeadMember
  have joinedHeadEqual : joinedHead = head := by
    have lookup := joinAtEndpoint_head? (second := second) firstHead
    rw [joinedHeadLookup] at lookup
    exact Option.some.inj lookup
  subst joinedHead
  cases first with
  | nil => simp at firstHead
  | cons firstPoint firstTail =>
      have firstPointEqual : firstPoint = head := by
        simpa using firstHead
      subst firstPoint
      simp only [LeanTrominoes.joinAtEndpoint,
        List.cons_append, List.tail_cons,
        List.mem_append] at joinedHeadMember
      rcases joinedHeadMember with firstMember | secondMember
      · exact fresh head (by simp) firstMember
      · exact headNotInSecondTail secondMember

/-- Endpoint isolation of a subdivided prefix extends across a correctly
matched subdivided suffix when the prefix's first endpoint is absent from
the suffix. -/
theorem HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
    {first second : List Cell} {head middle : Cell}
    (fresh : HeadNotInTail (unitSubdividePolyline first))
    (firstNonempty : first ≠ [])
    (firstHead : first.head? = some head)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (headNotInSecond : head ∉ unitSubdividePolyline second) :
    HeadNotInTail
      (unitSubdividePolyline
        (LeanTrominoes.joinAtEndpoint first second)) := by
  rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
    firstNonempty firstLast secondHead]
  apply fresh.joinAtEndpoint
  · rw [unitSubdividePolyline_head? firstNonempty, firstHead]
  · intro member
    exact headNotInSecond (List.mem_of_mem_tail member)

/-- Joining a prefix to a nondegenerate suffix preserves isolation of the
suffix's final endpoint when that endpoint is absent from the prefix. -/
theorem LastNotInDropLast.joinAtEndpoint
    {first second : List Cell} {middle last : Cell}
    (fresh : LastNotInDropLast second)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLast : second.getLast? = some last)
    (secondLength : 2 ≤ second.length)
    (lastNotInFirst : last ∉ first) :
    LastNotInDropLast
      (LeanTrominoes.joinAtEndpoint first second) := by
  intro joinedLast joinedLastLookup joinedLastMember
  have joinedLastEqual : joinedLast = last := by
    have lookup :=
      joinAtEndpoint_getLast? firstLast secondHead secondLast
    rw [joinedLastLookup] at lookup
    exact Option.some.inj lookup
  subst joinedLast
  cases second with
  | nil => simp at secondLength
  | cons secondFirst secondRest =>
      cases secondRest with
      | nil => simp at secondLength
      | cons secondNext secondTail =>
          have secondFresh :
              last ∉ (secondFirst :: secondNext :: secondTail).dropLast :=
            fresh last secondLast
          simp only [LeanTrominoes.joinAtEndpoint, List.tail_cons]
            at joinedLastMember
          rw [List.dropLast_append_of_ne_nil (by simp)]
            at joinedLastMember
          rcases List.mem_append.mp joinedLastMember with
            firstMember | secondMember
          · exact lastNotInFirst firstMember
          · apply secondFresh
            have secondRestNe :
                secondNext :: secondTail ≠ [] := by simp
            rw [List.dropLast_cons_of_ne_nil secondRestNe]
            exact List.mem_cons_of_mem secondFirst secondMember

/-- Final-endpoint isolation of a joined route restricts to its
nondegenerate suffix. -/
theorem LastNotInDropLast.of_joinAtEndpoint_right
    {first second : List Cell} {middle : Cell}
    (fresh :
      LastNotInDropLast
        (LeanTrominoes.joinAtEndpoint first second))
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLength : 2 ≤ second.length) :
    LastNotInDropLast second := by
  intro last secondLast secondMember
  have joinedLast :
      (LeanTrominoes.joinAtEndpoint first second).getLast? =
        some last :=
    joinAtEndpoint_getLast? firstLast secondHead secondLast
  apply fresh last joinedLast
  cases second with
  | nil => simp at secondLength
  | cons secondFirst secondRest =>
      cases secondRest with
      | nil => simp at secondLength
      | cons secondNext secondTail =>
          simp only [LeanTrominoes.joinAtEndpoint, List.tail_cons]
          rw [List.dropLast_append_of_ne_nil (by simp)]
          rw [List.dropLast_cons_of_ne_nil (by simp)] at secondMember
          simp only [List.mem_cons] at secondMember
          rcases secondMember with lastEqual | secondTailMember
          · have secondFirstEqual : secondFirst = middle := by
              simpa using secondHead
            rw [lastEqual, secondFirstEqual]
            exact
              List.mem_append.mpr
                (Or.inl (List.mem_of_mem_getLast? firstLast))
          · exact List.mem_append.mpr (Or.inr secondTailMember)

/-- The isolated final endpoint of a joined route is absent from its prefix
when the suffix contains an edge. -/
theorem LastNotInDropLast.not_mem_left_of_joinAtEndpoint
    {first second : List Cell} {middle last : Cell}
    (fresh :
      LastNotInDropLast
        (LeanTrominoes.joinAtEndpoint first second))
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLast : second.getLast? = some last)
    (secondLength : 2 ≤ second.length) :
    last ∉ first := by
  intro firstMember
  have joinedLast :
      (LeanTrominoes.joinAtEndpoint first second).getLast? =
        some last :=
    joinAtEndpoint_getLast? firstLast secondHead secondLast
  apply fresh last joinedLast
  cases second with
  | nil => simp at secondLength
  | cons secondFirst secondRest =>
      cases secondRest with
      | nil => simp at secondLength
      | cons secondNext secondTail =>
          simp only [LeanTrominoes.joinAtEndpoint, List.tail_cons]
          rw [List.dropLast_append_of_ne_nil (by simp)]
          exact List.mem_append.mpr (Or.inl firstMember)

/-- Any route containing a source edge still contains an edge after ordered
unit subdivision. -/
theorem unitSubdividePolyline_length_ge_two_of_length_ge_two
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    2 ≤ (unitSubdividePolyline points).length := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          exact unitSubdividePolyline_length_ge_two orthogonal

/-- Endpoint isolation of a subdivided suffix extends across a correctly
matched subdivided prefix when the final endpoint is absent from that
prefix. -/
theorem LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
    {first second : List Cell} {middle last : Cell}
    (fresh : LastNotInDropLast (unitSubdividePolyline second))
    (firstNonempty : first ≠ [])
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLast : second.getLast? = some last)
    (lastNotInFirst : last ∉ unitSubdividePolyline first) :
    LastNotInDropLast
      (unitSubdividePolyline
        (LeanTrominoes.joinAtEndpoint first second)) := by
  have secondNonempty : second ≠ [] := by
    intro secondEmpty
    simp [secondEmpty] at secondLength
  rw [LeanTrominoes.AxisDirection.unitSubdividePolyline_joinAtEndpoint
    firstNonempty firstLast secondHead]
  apply fresh.joinAtEndpoint
  · rw [unitSubdividePolyline_getLast?
      firstNonempty firstOrthogonal, firstLast]
  · rw [unitSubdividePolyline_head? secondNonempty, secondHead]
  · rw [unitSubdividePolyline_getLast?
      secondNonempty secondOrthogonal, secondLast]
  · exact
      unitSubdividePolyline_length_ge_two_of_length_ge_two
        secondLength secondOrthogonal
  · exact lastNotInFirst

end AxisDirection

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Contact-free continuous separation makes the ordered unit subdivisions
pointwise disjoint. -/
theorem RoutesStrictlyAvoidEachOther.unitSubdividePolyline_disjoint
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second) :
    List.Disjoint
      (AxisDirection.unitSubdividePolyline first)
      (AxisDirection.unitSubdividePolyline second) := by
  rw [List.disjoint_left]
  intro point firstMember secondMember
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        firstOrthogonal firstMember with
    firstOriginal | ⟨firstSegment, firstSegmentMember, firstInterior⟩
  · rcases
        AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
          secondOrthogonal secondMember with
      secondOriginal |
      ⟨secondSegment, secondSegmentMember, secondInterior⟩
    · exact strict.2.2.2 point firstOriginal point secondOriginal rfl
    · exact strict.2.1 point firstOriginal
        secondSegment secondSegmentMember secondInterior
  · rcases
        AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
          secondOrthogonal secondMember with
      secondOriginal |
      ⟨secondSegment, secondSegmentMember, secondInterior⟩
    · exact strict.2.2.1 point secondOriginal
        firstSegment firstSegmentMember firstInterior
    · exact strict.1 firstSegment firstSegmentMember
        secondSegment secondSegmentMember
        (GridSegment.interiorsMeet_of_interiorContains
          firstInterior secondInterior)

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace AxisDirection

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A simple terminal suffix has an isolated final endpoint after a
contact-free prefix, witnessed by any orthogonal route through that endpoint
which the prefix strictly avoids. -/
theorem
    lastNotInDropLast_unitSubdividePolyline_joinAtEndpoint_of_strictCycle
    {prefixRoute suffixRoute cycleRoute : List Cell}
    {middle target : Cell}
    (prefixNonempty : prefixRoute ≠ [])
    (suffixLength : 2 ≤ suffixRoute.length)
    (prefixOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline prefixRoute)
    (suffixOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline suffixRoute)
    (cycleOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline cycleRoute)
    (prefixLast : prefixRoute.getLast? = some middle)
    (suffixHead : suffixRoute.head? = some middle)
    (suffixLast : suffixRoute.getLast? = some target)
    (cycleLast : cycleRoute.getLast? = some target)
    (strict : RoutesStrictlyAvoidEachOther prefixRoute cycleRoute)
    (suffixSimple : LocalIncidenceDrawing.RouteIsSimple suffixRoute) :
    LastNotInDropLast
      (unitSubdividePolyline
        (LeanTrominoes.joinAtEndpoint prefixRoute suffixRoute)) := by
  have cycleNonempty : cycleRoute ≠ [] := by
    intro cycleEmpty
    simp [cycleEmpty] at cycleLast
  have cycleSubdividedLast :
      (unitSubdividePolyline cycleRoute).getLast? = some target := by
    rw [unitSubdividePolyline_getLast?
      cycleNonempty cycleOrthogonal, cycleLast]
  have targetInCycle : target ∈ unitSubdividePolyline cycleRoute :=
    mem_of_getLast?_eq_some cycleSubdividedLast
  have subdivisionsDisjoint :=
    strict.unitSubdividePolyline_disjoint
      prefixOrthogonal cycleOrthogonal
  have targetNotInPrefix :
      target ∉ unitSubdividePolyline prefixRoute := by
    intro targetInPrefix
    exact subdivisionsDisjoint targetInPrefix targetInCycle
  apply
    (lastNotInDropLast_unitSubdividePolyline_of_simple
      suffixOrthogonal suffixSimple)
      |>.unitSubdividePolyline_joinAtEndpoint
  · exact prefixNonempty
  · exact suffixLength
  · exact prefixOrthogonal
  · exact suffixOrthogonal
  · exact prefixLast
  · exact suffixHead
  · exact suffixLast
  · exact targetNotInPrefix

end AxisDirection
end LeanTrominoes

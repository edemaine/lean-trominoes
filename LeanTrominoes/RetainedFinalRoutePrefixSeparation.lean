/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.PeriodicGridDrawingRouteOccurrenceSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedPeriodicContinuousPlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointContacts
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteSimplicity

/-!
# Strict prefix separation in the final retained source

The final retained periodic drawing already supplies every geometric
certificate needed by the generic nonorthogonal route-occurrence theorem.
For two different stored routes, its route-simplicity theorem then removes
their final variable endpoints and upgrades endpoint-only contact to strict
prefix separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two different stored routes of the final retained source satisfy the
complete finite route-avoidance predicate in the base periodic cell. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
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
    (indicesDifferent : firstIndex ≠ secondIndex) :
    RoutesAvoidEachOther first second := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  have occurrenceDifferent :
      (firstIndex, ((0, 0) : Cell)) ≠
        (secondIndex, ((0, 0) : Cell)) := by
    intro equal
    exact indicesDifferent (congrArg Prod.fst equal)
  have translatedAvoid :=
    PeriodicGridDrawing.routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isContinuouslyPlanar
        formula wellFormed degree isLocal clausesNonempty)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsAvoidInteriors
        formula wellFormed degree isLocal clausesNonempty)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsMeetOnlyAtEndpoints
        formula wellFormed degree isLocal clausesNonempty)
      firstMember secondMember firstLength secondLength
      (0, 0) (0, 0) occurrenceDifferent
  have mapAddZero (points : List Cell) :
      points.map (Cell.add (0, 0)) = points := by
    induction points with
    | nil => rfl
    | cons point points induction =>
        rw [List.map_cons, induction]
        simp [Cell.add]
  have zeroTranslation :
      drawing.periodTranslation (0, 0) = (0, 0) := by
    simp [drawing, PeriodicGridDrawing.periodTranslation,
      Cell.scale]
  rw [zeroTranslation, mapAddZero, mapAddZero] at translatedAvoid
  exact translatedAvoid

/-- Two different stored routes of the final retained source are completely
contact-free when none of their advertised source and variable endpoints
coincide. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routesStrictlyAvoidEachOther_of_endpoints_ne
    {Variable : Type*} [DecidableEq Variable]
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
    (lastLastNe : first.getLast? ≠ second.getLast?) :
    RoutesStrictlyAvoidEachOther first second := by
  apply routesStrictlyAvoidEachOther_of_avoid_of_endpoints_ne
  · exact
      retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
        formula wellFormed degree isLocal clausesNonempty
        firstMember secondMember firstLength secondLength
        indicesDifferent
  · exact headHeadNe
  · exact headLastNe
  · exact lastHeadNe
  · exact lastLastNe

/-- Two different stored routes of the final retained source have strictly
separated `dropLast` prefixes whenever their clause-side endpoints differ. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
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
    RoutesStrictlyAvoidEachOther
      first.dropLast second.dropLast := by
  have avoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent
  have firstSimple :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      first (List.fst_mem_of_mem_zipIdx firstMember)
  have secondSimple :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      second (List.fst_mem_of_mem_zipIdx secondMember)
  exact
    routesStrictlyAvoidEachOther_dropLast_of_avoid_of_nodup_of_heads_ne
      avoid firstSimple.1 secondSimple.1 headsDifferent

/-- For two different final retained source routes, endpoint-only contact
and simplicity clear the first retained prefix from the second route's
variable endpoint whenever that endpoint differs from the first clause
endpoint. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_avoids_otherFinal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondFinal : Cell}
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
    (firstHead : first.head? = some firstSource)
    (secondLast : second.getLast? = some secondFinal)
    (sourceNeFinal : firstSource ≠ secondFinal) :
    (∀ point ∈ first.dropLast, point ≠ secondFinal) ∧
      ∀ segment ∈ gridPolylineSegments first.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains secondFinal := by
  have avoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent
  have firstSimple :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      first (List.fst_mem_of_mem_zipIdx firstMember)
  exact
    routePrefix_avoids_other_final_point_of_avoid
      avoid firstSimple.1 firstHead secondLast sourceNeFinal

/-- Complete route avoidance still separates the first retained prefix from
the second final segment when the two prefixes may share their head, provided
the second segment's entrance is not that shared head. -/
private theorem
    routesStrictlyAvoidEachOther_dropLast_finalSegment_of_head_contacts
    {first second : List Cell}
    {secondEntrance secondFinal : Cell}
    (avoid : RoutesAvoidEachOther first second)
    (prefixContacts :
      RoutesMeetOnlyAtHeads first.dropLast second.dropLast)
    (secondEntranceEq :
      second.dropLast.getLast? = some secondEntrance)
    (secondFinalEq :
      second.getLast? = some secondFinal)
    (firstPointsAvoidFinal :
      ∀ point ∈ first.dropLast, point ≠ secondFinal)
    (secondEntranceNotHead :
      second.dropLast.head? ≠ some secondEntrance) :
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
      rcases terminalPointMember with rfl | rfl
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
    · intro equal
      exact secondEntranceNotHead
        (prefixContacts
          firstPoint firstPointMember
          terminalPoint secondEntranceMember equal).2
    · exact
        firstPointsAvoidFinal
          firstPoint firstPointMember

/-- A duplicate-free list whose head and last are the same named point is a
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

/-- The first retained prefix is strictly separated from the second route's
discarded final source segment.  This is the exact unscaled corridor axis
used by the replacement outer fan. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherFinalSegment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondFinal : Cell}
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
    (secondLast : second.getLast? = some secondFinal)
    (sourceNeFinal : firstSource ≠ secondFinal) :
    RoutesStrictlyAvoidEachOther
      first.dropLast
      [polylineLastEntrance second, secondFinal] := by
  have avoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent
  have prefixesAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  have finalClearance :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_avoids_otherFinal
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent firstHead secondLast sourceNeFinal
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length
      second secondLength
  have entranceEq :
      second.dropLast.getLast? =
        some (polylineLastEntrance second) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  exact
    routesStrictlyAvoidEachOther_dropLast_finalSegment
      avoid prefixesAvoid entranceEq secondLast
      finalClearance.1

/-- The head-aware variant for two routes of one clause.  Their retained
prefixes may meet at the common clause head, but a non-singleton second
prefix puts its final-segment entrance elsewhere, so that legal contact
cannot reach the discarded terminal segment. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherFinalSegment_of_secondPrefix_length_ne_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondFinal : Cell}
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
    (firstHead : first.head? = some firstSource)
    (secondLast : second.getLast? = some secondFinal)
    (sourceNeFinal : firstSource ≠ secondFinal)
    (secondPrefixLengthNeOne :
      second.dropLast.length ≠ 1) :
    RoutesStrictlyAvoidEachOther
      first.dropLast
      [polylineLastEntrance second, secondFinal] := by
  have avoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent
  have firstSimple :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      first (List.fst_mem_of_mem_zipIdx firstMember)
  have secondSimple :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal clausesNonempty
      second (List.fst_mem_of_mem_zipIdx secondMember)
  have prefixContacts :
      RoutesMeetOnlyAtHeads first.dropLast second.dropLast :=
    routePrefix_contactsAtHeads_of_avoid_of_nodup
      avoid firstSimple.1 secondSimple.1
  have finalClearance :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_avoids_otherFinal
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent firstHead secondLast sourceNeFinal
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length
      second secondLength
  have entranceEq :
      second.dropLast.getLast? =
        some (polylineLastEntrance second) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have secondPrefixNodup : second.dropLast.Nodup := by
    have appended :
        (second.dropLast ++ [secondFinal]).Nodup := by
      rw [List.dropLast_append_getLast?
        secondFinal secondLast]
      exact secondSimple.1
    exact appended.of_append_left
  have entranceNotHead :
      second.dropLast.head? ≠
        some (polylineLastEntrance second) := by
    intro headEq
    apply secondPrefixLengthNeOne
    exact
      list_length_eq_one_of_nodup_of_head_last_eq
        secondPrefixNodup headEq entranceEq
  exact
    routesStrictlyAvoidEachOther_dropLast_finalSegment_of_head_contacts
      avoid prefixContacts entranceEq secondLast
      finalClearance.1 entranceNotHead

end PeriodicOrthocrossing
end LeanTrominoes

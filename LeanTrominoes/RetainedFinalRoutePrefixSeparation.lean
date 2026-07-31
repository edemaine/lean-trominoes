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

end PeriodicOrthocrossing
end LeanTrominoes

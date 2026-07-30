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
  have avoid : RoutesAvoidEachOther first second := by
    rw [zeroTranslation, mapAddZero, mapAddZero] at translatedAvoid
    exact translatedAvoid
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

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.RetainedAngularFanFinalCoordinatedExpandedBounds
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts

/-!
# Expanded-period bounds for normalized final routes

Route normalization unit-subdivides each coordinated orthogonal polyline and
then erases loops.  Every retained point is consequently either an original
route point or an interior point of an original axis-aligned segment.  The
open neighboring-period square is orthogonally convex, so the coordinated
expanded-period bound survives normalization.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- A point on an axis-aligned segment whose endpoints lie strictly in an
open coordinate square lies strictly in the same square. -/
private theorem point_inExpanded_of_contains
    {period : Int}
    {segment : GridSegment}
    {point : Cell}
    (startBounded :
      -period < segment.start.1 ∧
        segment.start.1 < 2 * period ∧
        -period < segment.start.2 ∧
        segment.start.2 < 2 * period)
    (finishBounded :
      -period < segment.finish.1 ∧
        segment.finish.1 < 2 * period ∧
        -period < segment.finish.2 ∧
        segment.finish.2 < 2 * period)
    (contains : segment.Contains point) :
    -period < point.1 ∧
      point.1 < 2 * period ∧
      -period < point.2 ∧
      point.2 < 2 * period := by
  rcases startBounded with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounded with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases contains with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · rcases between with between | between <;>
      simp only [GridSegment.IsHorizontal] at horizontal <;>
      omega
  · rcases between with between | between <;>
      simp only [GridSegment.IsVertical] at vertical <;>
      omega

/-- Every point of every genuine normalized final fixed-eight route lies in
the open neighboring-period square of the public refined placement. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) :
    let refinedPeriod : Int :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  let rawRoute :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex
  have valid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawHead :
      rawRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              formula)
            clause) := by
    simpa only [rawRoute] using valid.1
  have rawNonempty : rawRoute ≠ [] := by
    intro rawEmpty
    rw [rawEmpty] at rawHead
    simp at rawHead
  have rawOrthogonal : OrthogonalPolyline rawRoute := by
    simpa only [rawRoute] using valid.2.2
  have rawBounded :
      ∀ rawPoint ∈ rawRoute,
        let refinedPeriod : Int :=
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).period;
        -refinedPeriod < rawPoint.1 ∧
          rawPoint.1 < 2 * refinedPeriod ∧
          -refinedPeriod < rawPoint.2 ∧
          rawPoint.2 < 2 * refinedPeriod := by
    intro rawPoint rawPointMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        rawPointMember
  have subdividedMember :
      point ∈ AxisDirection.unitSubdividePolyline rawRoute :=
    (AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      rawNonempty rawOrthogonal).subset
      (by
        simpa only [
          retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes,
          rawRoute] using pointMember)
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        rawOrthogonal subdividedMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact rawBounded point originalMember
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    exact
      point_inExpanded_of_contains
        (rawBounded segment.start endpoints.1)
        (rawBounded segment.finish endpoints.2)
        (GridSegment.contains_of_interiorContains interior)

end PeriodicOrthocrossing
end LeanTrominoes

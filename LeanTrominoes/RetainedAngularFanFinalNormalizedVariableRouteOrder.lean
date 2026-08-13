/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingLoopErasureRouteOrders
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteLength
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalRouteEndpointIsolation

/-!
# Variable route order after final fixed-eight normalization

The final coordinated routes already follow occurrence order.  Their
nondegeneracy, orthogonality, and variable-endpoint isolation ensure that
verified unit subdivision and loop erasure preserve every terminal direction,
so the normalized simple route family has the same clockwise order.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

private theorem length_ge_two_of_distinct_endpoints
    {points : List Cell} {first last : Cell}
    (head : points.head? = some first)
    (getLast : points.getLast? = some last)
    (distinct : first ≠ last) :
    2 ≤ points.length := by
  cases points with
  | nil => simp at head
  | cons point rest =>
      cases rest with
      | nil =>
          have firstEqual : first = point :=
            (Option.some.inj head).symm
          have lastEqual : point = last :=
            Option.some.inj getLast
          exact (distinct (firstEqual.trans lastEqual)).elim
      | cons next tail => simp

private theorem endpoints_distinct_of_lastNotInDropLast
    {points : List Cell} {first last : Cell}
    (length : 2 ≤ points.length)
    (fresh : AxisDirection.LastNotInDropLast points)
    (head : points.head? = some first)
    (getLast : points.getLast? = some last) :
    first ≠ last := by
  intro equal
  subst last
  apply fresh first getLast
  cases points with
  | nil => simp at length
  | cons point rest =>
      cases rest with
      | nil => simp at length
      | cons next tail =>
          have pointEqual : point = first :=
            Option.some.inj head
          simp [pointEqual]

/-- Pointwise normalization preserves the clockwise occurrence order of the
final coordinated fixed-eight route family. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source) := by
  apply
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).normalizeOrthogonalIncidenceRoutes_of_lastNotInDropLast
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastNotInDropLast
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember

/-- Every genuine normalized fixed-eight route still contains an edge. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).length := by
  let route :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      source clauseIndex literalIndex
  let subdivided := AxisDirection.unitSubdividePolyline route
  have routeLength :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have routeValid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have subdividedLength : 2 ≤ subdivided.length :=
    AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
      routeLength routeValid.2.2
  have subdividedHead :
      subdivided.head? = route.head? := by
    rw [AxisDirection.unitSubdividePolyline_head?
      (points := route) (by
        intro empty
        simp [route, empty] at routeLength)]
  have subdividedLast :
      subdivided.getLast? = route.getLast? := by
    rw [AxisDirection.unitSubdividePolyline_getLast?
      (points := route) (by
        intro empty
        simp [route, empty] at routeLength)
      routeValid.2.2]
  have endpointsDistinct :
      PositionedPeriodicCNF.canonicalClausePosition
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source) clause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            source) clause literal := by
    apply endpoints_distinct_of_lastNotInDropLast
      subdividedLength
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastNotInDropLast
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
    · rw [subdividedHead, routeValid.1]
    · rw [subdividedLast, routeValid.2.1]
  have normalizedValid :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  exact length_ge_two_of_distinct_endpoints
    normalizedValid.1 normalizedValid.2.1 endpointsDistinct

end PeriodicOrthocrossing
end LeanTrominoes

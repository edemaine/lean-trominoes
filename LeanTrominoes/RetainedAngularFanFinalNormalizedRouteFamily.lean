/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteFamily

/-!
# The normalized final route family

The final coordinated incidence routes are orthogonal lattice walks with the
right canonical endpoints, but some collar walks revisit lattice points.
This file applies verified unit-grid loop erasure pointwise.  Every genuine
incidence retains its canonical endpoints and orthogonality and becomes a
geometrically simple route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Pointwise unit subdivision and loop erasure of the final coordinated
incidence-route family. -/
def
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    AxisDirection.normalizeOrthogonalPolyline
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)

/-- Every genuine normalized incidence has the same canonical endpoints as
the coordinated source route and remains orthogonal. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              formula)
            clause) ∧
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula)
              clause literal) ∧
      OrthogonalPolyline
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) := by
  let route :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex
  have valid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  have normalizedHead :=
    AxisDirection.normalizeOrthogonalPolyline_head?
      nonempty valid.2.2
  have normalizedLast :=
    AxisDirection.normalizeOrthogonalPolyline_getLast?
      nonempty valid.2.2
  have normalizedOrthogonal :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      nonempty valid.2.2
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes,
    route] using
      ⟨normalizedHead.trans valid.1,
        normalizedLast.trans valid.2.1,
        normalizedOrthogonal⟩

/-- Every genuine route in the normalized final family is geometrically
simple: it has no repeated point, no listed point in a nonincident segment
interior, and no two distinct segment interiors meet. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_isSimple
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex) := by
  let route :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex
  have valid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_isSimple
        nonempty valid.2.2

/-- Every genuine route in the normalized final family consists entirely
of genuine unit lattice steps. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  let route :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex
  have valid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_unitSteps
        nonempty valid.2.2

/-- The normalized final route family, packaged with canonical endpoints and
pointwise orthogonality. -/
def
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitCanonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula) where
  routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes

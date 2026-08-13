/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalNormalizedDrawing

/-!
# Normalized coordinated unit-free exact-one routes

The ribbon construction consumes the final unit-free exact-one formula, not
the earlier fixed-eight formula.  This module therefore applies verified
orthogonal loop erasure once more at that final interface.  Canonical
endpoints and orthogonality survive, every genuine route is a simple unit-step
path, and the assembled drawing has exact graph endpoints and integer-grid
planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The normalized route family installed at the final unit-free exact-one
interface. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Expose final normalization without unfolding the large canonical route
certificate during drawing assembly. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_eq_normalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty =
      PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rfl

/-- Every genuine final normalized exact-one route has canonical endpoints
and remains orthogonal. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let route :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
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
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      ⟨normalizedHead.trans valid.1,
        normalizedLast.trans valid.2.1,
        normalizedOrthogonal⟩

/-- Every genuine final normalized exact-one route is a simple path. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex) := by
  let route :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_isSimple
        nonempty valid.2.2

/-- Every genuine final normalized exact-one route consists of unit axis
steps. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  let route :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_unitSteps
        nonempty valid.2.2

/-- Pointwise-normalized canonical routes for the final coordinated unit-free
exact-one formula. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source) where
  routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- The assembled coordinated unit-free exact-one drawing before final route
normalization. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The assembled final normalized unit-free exact-one drawing. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The final exact-one drawing is drawing-level normalization of the
coordinated predecessor. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_eq_normalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty =
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).normalizeOrthogonalRoutes := by
  rw [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_eq_normalize]
  exact PositionedPeriodicCNF.incidenceDrawing_normalizeOrthogonalRoutes
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The final normalized exact-one drawing realizes every incidence-graph
edge. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).RoutesMatch
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase.incidenceGraph := by
  rw [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_eq_normalize,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing]
  exact
    PositionedPeriodicCNF.routesMatch_incidenceDrawing_normalizeOrthogonalRoutes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- The final normalized exact-one drawing is orthogonal. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsOrthogonal := by
  rw [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_eq_normalize,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing]
  exact
    PositionedPeriodicCNF.isOrthogonal_incidenceDrawing_normalizeOrthogonalRoutes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Every stored route in the final normalized exact-one drawing consists of
unit axis steps. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).HasUnitSteps := by
  rw [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_hasUnitSteps_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Every stored route of the final normalized exact-one drawing is a
geometrically simple path. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ route ∈
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  rw [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_routesSimple_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Unit steps give unconditional integer-grid planarity of the final
normalized exact-one drawing. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsPlanar :=
  PeriodicGridDrawing.isPlanar_of_hasUnitSteps
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Once complete separation is established pairwise for distinct lifted
route occurrences, the normalized final exact-one drawing is ribbon-ready.
The bridge discharges both global indexed-occurrence predicates and handles
self-comparisons using route simplicity. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_liftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).LiftedRoutesAvoidEachOther) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_liftedRoutesAvoidEachOther
    separated
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_routesSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- It suffices to separate every pair after fixing the first normalized
route in the fundamental representative and translating only the second by
one relative lattice offset. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).RelativeLiftedRoutesAvoidEachOther) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    separated
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_routesSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The remaining pairwise geometry may be proved directly on genuine final
clause/literal incidences; the generic lookup bridge restores their anonymous
flat drawing indices. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_relativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rw [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing]
  exact
    PositionedPeriodicCNF.incidenceDrawing_relativeLiftedRoutesAvoidEachOther
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
        source)
      separated

/-- It is enough to establish relative separation before final loop erasure.
Canonical endpoints make every genuine raw route nonempty, and the raw
construction already supplies the orthogonality needed by the generic
normalization transport theorem. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_rawRelativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsNormalizedIncidenceDrawing_isRibbonReady_of_relativeIncidenceRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  apply separated.normalizeOrthogonalIncidenceRoutes
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    intro routeEmpty
    have headNonempty := valid.1
    have routeEmpty' :
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty incidence.1.clauseIndex
            incidence.1.literalIndex = [] := by
      simpa using routeEmpty
    simp [routeEmpty'] at headNonempty
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes

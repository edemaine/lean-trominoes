import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalNormalizedDrawing

/-!
# Normalized ordered Figure 9 routes

The ordered composed family removes local source-clause crossings before the
two exact-one transformations are spliced together.  This module applies
verified orthogonal loop erasure to that family.  Canonical endpoints and
orthogonality survive, every genuine route becomes a simple unit-step path,
and the assembled drawing has exact graph endpoints and integer-grid
planarity.  Complete relative separation remains the one premise needed by
the supplied bridge to ribbon readiness.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance orderedComposedVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The ordered two-stage Figure 9 placement inherits the positive period of
the retained fixed-eight source drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period := by
  unfold
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
  apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
  apply PeriodicOneInThreePositioned.placement_period_pos
  exact
    retainedFigureNineClearancePlacement_period_pos source

/-- The normalized route family installed at the final unit-free exact-one
interface. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Expose final normalization without unfolding the large canonical route
certificate during drawing assembly. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_eq_normalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty =
      PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  rfl

/-- Every genuine final normalized exact-one route has canonical endpoints
and remains orthogonal. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_valid
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
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause) ∧
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let route :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
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
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      ⟨normalizedHead.trans valid.1,
        normalizedLast.trans valid.2.1,
        normalizedOrthogonal⟩

/-- Every genuine final normalized exact-one route is a simple path. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_isSimple
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
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex) := by
  let route :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_isSimple
        nonempty valid.2.2

/-- Every genuine final normalized exact-one route consists of unit axis
steps. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_unitSteps
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
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex).IsChain
        AxisDirection.IsUnitAxisStep := by
  let route :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have valid :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have nonempty : route ≠ [] := by
    intro routeEmpty
    have := valid.1
    simp [route, routeEmpty] at this
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes,
    route] using
      AxisDirection.normalizeOrthogonalPolyline_unitSteps
        nonempty valid.2.2

/-- The ordered composed routes packaged with their canonical endpoint and
orthogonality certificates before final loop erasure. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source) where
  routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- Pointwise-normalized canonical routes for the final ordered unit-free
exact-one formula. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source) where
  routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- The assembled coordinated unit-free exact-one drawing before final route
normalization. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The ordered raw composed drawing realizes every incidence-graph edge. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).RoutesMatch
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.incidenceGraph := by
  exact
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routesMatch
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
          source)

/-- The ordered raw composed drawing is orthogonal. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsOrthogonal := by
  exact
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).isOrthogonal

/-- The assembled final normalized unit-free exact-one drawing. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The final exact-one drawing is drawing-level normalization of the
coordinated predecessor. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_eq_normalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty =
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).normalizeOrthogonalRoutes := by
  rw [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_eq_normalize]
  exact PositionedPeriodicCNF.incidenceDrawing_normalizeOrthogonalRoutes
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The final normalized exact-one drawing realizes every incidence-graph
edge. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).RoutesMatch
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.incidenceGraph := by
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_eq_normalize,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing]
  exact
    PositionedPeriodicCNF.routesMatch_incidenceDrawing_normalizeOrthogonalRoutes
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_routesMatch
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_isOrthogonal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- The final normalized exact-one drawing is orthogonal. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsOrthogonal := by
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_eq_normalize,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing]
  exact
    PositionedPeriodicCNF.isOrthogonal_incidenceDrawing_normalizeOrthogonalRoutes
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_routesMatch
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceDrawing_isOrthogonal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Every stored route in the final normalized exact-one drawing consists of
unit axis steps. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_hasUnitSteps
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).HasUnitSteps := by
  rw [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_hasUnitSteps_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_unitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Every stored route of the final normalized exact-one drawing is a
geometrically simple path. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ route ∈
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_routesSimple_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Unit steps give unconditional integer-grid planarity of the final
normalized exact-one drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsPlanar :=
  PeriodicGridDrawing.isPlanar_of_hasUnitSteps
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Once complete separation is established pairwise for distinct lifted
route occurrences, the normalized final exact-one drawing is ribbon-ready.
The bridge discharges both global indexed-occurrence predicates and handles
self-comparisons using route simplicity. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_liftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).LiftedRoutesAvoidEachOther) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_liftedRoutesAvoidEachOther
    separated
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_routesSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- It suffices to separate every pair after fixing the first normalized
route in the fundamental representative and translating only the second by
one relative lattice offset. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).RelativeLiftedRoutesAvoidEachOther) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    separated
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_routesSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_hasUnitSteps
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- The remaining pairwise geometry may be proved directly on genuine final
clause/literal incidences; the generic lookup bridge restores their anonymous
flat drawing indices. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_relativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing]
  exact
    PositionedPeriodicCNF.incidenceDrawing_relativeLiftedRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
        source)
      separated

/-- It is enough to establish relative separation before final loop erasure.
Canonical endpoints make every genuine raw route nonempty, and the raw
construction already supplies the orthogonality needed by the generic
normalization transport theorem. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_rawRelativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (separated :
      PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_relativeIncidenceRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  apply separated.normalizeOrthogonalIncidenceRoutes
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    have valid :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    intro routeEmpty
    have headNonempty := valid.1
    have routeEmpty' :
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty incidence.1.clauseIndex
            incidence.1.literalIndex = [] := by
      simpa using routeEmpty
    simp [routeEmpty'] at headNonempty
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    exact
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes

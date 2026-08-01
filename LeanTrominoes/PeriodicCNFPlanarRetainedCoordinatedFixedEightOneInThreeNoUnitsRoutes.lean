import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeWrappedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Unit elimination over coordinated retained exact-one routes

The wrapped coordinated Figure 9 routes are inherited by the positioned
unit-elimination construction.  Its generic local-route adapter completes
all fresh auxiliary incidences.  The resulting unit-free exact-one route
family has canonical endpoints, is orthogonal, and realizes every incidence
graph edge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Final positioned unit-free exact-one formula over the coordinated
retained fixed-eight geometry. -/
def
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source)

/-- Placement of the final coordinated unit-free exact-one formula. -/
def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)

@[simp]
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase =
      PeriodicOneInThreeNoUnits.formula
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (retainedDrawingEightOccurrenceSplitFormula source))) := by
  simp [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula]

/-- Unit elimination preserves coordinated Figure 9 atom distinctness. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).AllAtomsNodup :=
  PeriodicOneInThreeNoUnitsPositioned.formula_allAtomsNodup
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source)
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      source)

/-- Every final coordinated exact-one clause has arity two or three. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase := by
  rw [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- The full coordinated fixed-eight exact-one pipeline has positive
physical period. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source).period := by
  unfold
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
  apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
  change
    0 <
      (PeriodicOneInThreePositioned.placement
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source)).period
  apply PeriodicOneInThreePositioned.placement_period_pos
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
      source

/-- Unit-elimination suffixes inherited from the wrapped coordinated
Figure 9 routes. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (PeriodicOneInThreeNoUnitsPositioned.normalizedLocalEndpoint
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement
          source)) :=
  PeriodicOneInThreeNoUnitsPositioned.inheritedRouteSuffixes
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
      source)
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      let valid :=
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember
      ⟨valid.1, valid.2.1⟩)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)

/-- Complete local-plus-inherited routes for the final coordinated
unit-free exact-one formula. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreeNoUnitsPositioned.splicedRoutes
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine final coordinated unit-free exact-one route has canonical
endpoints and is orthogonal. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
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
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement] using
    PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_valid_of_members
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
        source)
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

/-- The final coordinated route family packaged with pointwise canonical
endpoint and orthogonality certificates. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
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
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- The complete final coordinated routes match every incidence-graph
edge. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).RoutesMatch
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase.incidenceGraph := by
  exact
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routesMatch
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
          source)

/-- The assembled final coordinated unit-free exact-one drawing is
orthogonal. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).IsOrthogonal := by
  exact
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).isOrthogonal

end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreeWrappedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Unit-elimination routes over retained fixed-eight exact-one SAT

The complete wrapped retained Figure 9 routes are inherited by the positioned
unit-elimination construction, which also supplies certified local routes for
its fresh auxiliaries.  The final unit-free exact-one incidence drawing has
exact periodic endpoints and is orthogonal.  Its global planarity still rests
on the coordinated retained split boundary prefixes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Inherited unit-elimination suffixes obtained from the wrapped retained
Figure 9 routes. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source))
      (PeriodicOneInThreeNoUnitsPositioned.placement
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedFixedEightPeriodicPlanarOneInThreePlacement source))
      (PeriodicOneInThreeNoUnitsPositioned.normalizedLocalEndpoint
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedFixedEightPeriodicPlanarOneInThreePlacement source)) :=
  PeriodicOneInThreeNoUnitsPositioned.inheritedRouteSuffixes
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
    (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
      source)
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      source)
    (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      let valid :=
        retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember
      ⟨valid.1, valid.2.1⟩)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)

/-- Complete local-plus-inherited routes for the final retained unit-free
exact-one formula. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreeNoUnitsPositioned.splicedRoutes
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
    (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
    (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine final retained unit-free exact-one route has exact
canonical endpoints and is orthogonal. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
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
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause) ∧
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
      retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement] using
    PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_valid_of_members
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
        source)
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

/-- The final retained route family packaged with pointwise canonical
endpoint and orthogonality certificates. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source) where
  routes :=
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- The complete final retained routes match every incidence-graph edge. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).RoutesMatch
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase.incidenceGraph := by
  exact
    (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).routesMatch
        (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
          source)

/-- The assembled final retained unit-free exact-one drawing is
orthogonal. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).IsOrthogonal := by
  exact
    (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).isOrthogonal

end PeriodicOrthocrossing
end LeanTrominoes

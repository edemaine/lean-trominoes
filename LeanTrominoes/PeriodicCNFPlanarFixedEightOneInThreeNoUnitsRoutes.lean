/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeWrappedRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamily
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Complete unit-elimination routes over the fixed-eight hardness pipeline

This file reuses the complete wrapped Figure 9 routes as the inherited
source routes for unit elimination, then splices in the local no-unit
gadgets.  The resulting final route family has exact canonical endpoints
and is orthogonal.  Its inherited routes connect the new local ports directly
to the transformed first exits of the Figure 9 routes, removing the replaced
Figure 9 clause points.

The remaining generic port-to-exit detours are not yet coordinated into a
global noncrossing fan, so this construction does not yet claim planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Complete inherited unit-elimination suffixes obtained from the wrapped
fixed-eight Figure 9 routes. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input))
      (PeriodicOneInThreeNoUnitsPositioned.placement
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input)
        (drawingFixedEightPeriodicPlanarOneInThreePlacement input))
      (PeriodicOneInThreeNoUnitsPositioned.normalizedLocalEndpoint
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input)
        (drawingFixedEightPeriodicPlanarOneInThreePlacement input)) :=
  PeriodicOneInThreeNoUnitsPositioned.inheritedRouteSuffixes
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
    (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
      input)
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      input)
    (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
      input sourceLocal sourceWidth sourceOccurrences)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      let valid :=
        drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
          input sourceLocal sourceWidth sourceOccurrences
          sourceClauseMember sourceLiteralMember
      ⟨valid.1, valid.2.1⟩)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
        input sourceLocal sourceWidth sourceOccurrences
        sourceClauseMember sourceLiteralMember).2.2)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
        input sourceLocal sourceWidth sourceOccurrences
        sourceClauseMember sourceLiteralMember)

/-- Complete local-plus-inherited routes for the final fixed-eight,
unit-free exact-one formula. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreeNoUnitsPositioned.splicedRoutes
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
    (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
    (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
      input sourceLocal sourceWidth sourceOccurrences)

/-- Every genuine final fixed-eight unit-free exact-one route has exact
canonical endpoints and is orthogonal. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              input)
            clause) ∧
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              input)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          input sourceLocal sourceWidth sourceOccurrences
          clauseIndex literalIndex) := by
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
      drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
      drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement] using
    PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_valid_of_members
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
      (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
        input)
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
        input sourceLocal sourceWidth sourceOccurrences)
      clauseMember literalMember

/-- The final fixed-eight route family packaged with its complete pointwise
canonical endpoint and orthogonality certificates. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        input) where
  routes :=
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
      input sourceLocal sourceWidth sourceOccurrences
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        input sourceLocal sourceWidth sourceOccurrences
        clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_valid
        input sourceLocal sourceWidth sourceOccurrences
        clauseMember literalMember).2.2

/-- The complete final routes match every edge of the fixed-eight,
unit-free exact-one incidence graph. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)).RoutesMatch
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input).erase.incidenceGraph := by
  exact
    (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      input sourceLocal sourceWidth sourceOccurrences).routesMatch
        (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
          input)

/-- The assembled final fixed-eight unit-free exact-one incidence drawing is
orthogonal. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)).IsOrthogonal := by
  exact
    (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsCanonicalRoutes
      input sourceLocal sourceWidth sourceOccurrences).isOrthogonal

end PeriodicOrthocrossing
end LeanTrominoes

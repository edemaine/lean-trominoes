import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily

/-!
# Ordered Figure 9 routes over the retained fixed-eight source

The retained source clauses are first reordered by clockwise exit direction.
Their certified finite connector fans can then join the three fixed Figure 9
ports to the inherited source-route exits without local crossings.  This file
instantiates the generic ordered suffix family and completes it with the local
routes for both clause-replacement stages.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- The twice-replaced raw formula built from the clockwise-ordered retained
source presentation. -/
def
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (PeriodicOneInThreePositioned.formula
      (retainedFigureNineClearancePositionedFormula source))

/-- The two-stage Figure 9 placement over the ordered retained source. -/
def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.composedPlacement
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)

/-- Direct original-source suffixes selected from the valid ordered connector
fan of each retained source clause. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :=
  PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixes
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedFigureNineClearanceIncidenceRoutes source)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        sourceClauseNonempty =>
      retainedFigureNineClearance_clauseExitFanData_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceClauseNonempty)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      let valid :=
        retainedFigureNineClearanceIncidenceRoutes_valid
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember
      ⟨valid.1, valid.2.1⟩)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      (retainedFigureNineClearanceIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedFigureNineClearanceIncidenceRoutes_exits
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedFigureNineClearanceIncidenceRoutes_unitSteps
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember)

/-- Complete twice-replaced routes obtained by splicing the ordered inherited
suffixes onto the certified local Figure 9 and unit-elimination routes. -/
noncomputable def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PlanarOneInThreeNoUnitsFigureNine.splicedRoutes
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine ordered composed route has exact canonical endpoints and is
orthogonal. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
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
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause) ∧
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_valid_of_members
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedFigureNineClearancePositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedClauseRouteOrder
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineBinaryClauseRouteOrder

/-! # Binary Figure 9 clause order after final loop erasure -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance binaryNormalizedClauseOrderVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem polyline_length_ge_two_of_firstDirection_genuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

private theorem unitSubdividePolyline_length_ge_two_of_length_ge_two
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal : OrthogonalPolyline points) :
    2 ≤ (AxisDirection.unitSubdividePolyline points).length := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          exact
            AxisDirection.unitSubdividePolyline_length_ge_two
              (first := first) (second := second)
              (rest := rest) orthogonal

/-- Before loop erasure, a genuine binary incidence retains the finite
template's west/east first direction. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_firstDirection_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) =
      AxisDirection.binaryUnitEliminationClauseExitDirection
        literalIndex := by
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_firstDirection_of_binary
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
        clauseMember arity literalMember

/-- A binary incidence is local to the replacement gadgets, so its simple
local route gives an isolated start point before final loop erasure. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_headNotInTail_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex)) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex literalIndex
  have notInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        literal.atom ≠ .inl (.inl sourceAtom) :=
    PlanarOneInThreeNoUnitsFigureNine.binaryClause_literal_not_original
      clearanceSource clauseMember arity
      (List.fst_mem_of_mem_zipIdx literalMember)
  have rawEq :=
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember notInherited
  have localOrthogonal : OrthogonalPolyline localRoute := by
    simpa only [localRoute] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember literalMember
  have localSimple : LocalIncidenceDrawing.RouteIsSimple localRoute := by
    simpa only [localRoute] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_isSimple_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember literalMember
  rw [rawEq]
  exact
    AxisDirection.headNotInTail_unitSubdividePolyline_of_simple
      localOrthogonal localSimple

/-- Final loop erasure preserves the finite west/east first direction of a
binary generated clause. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) =
      AxisDirection.binaryUnitEliminationClauseExitDirection
        literalIndex := by
  let rawRoute :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have rawDirection :
      AxisDirection.polylineFirstDirection rawRoute =
        AxisDirection.binaryUnitEliminationClauseExitDirection
          literalIndex := by
    simpa only [rawRoute] using
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_firstDirection_of_binary
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember arity literalMember
  have routeOrthogonal : OrthogonalPolyline rawRoute := by
    simpa only [rawRoute] using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  have routeFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline rawRoute) := by
    simpa only [rawRoute] using
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_headNotInTail_of_binary
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember arity literalMember
  have rawLength : 2 ≤ rawRoute.length :=
    polyline_length_ge_two_of_firstDirection_genuine (by
      rw [rawDirection]
      exact
        AxisDirection.binaryUnitEliminationClauseExitDirection_isGenuine
          literalIndex)
  have normalizedDirection :=
    AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
      (unitSubdividePolyline_length_ge_two_of_length_ge_two
        rawLength routeOrthogonal)
      routeOrthogonal routeFresh
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_eq_normalize]
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline rawRoute) = _
  exact normalizedDirection.trans rawDirection

/-- Thus the semantic stable clockwise sort of a binary generated clause is
exactly old literal order `1,0`. -/
theorem
    retainedOrderedFixedEight_orderClauseByRouteDirection_literals_eq_one_zero_of_binary
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
    {first second :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (literalsEq : clause.literals = [first, second]) :
    (PositionedPeriodicCNF.orderClauseByRouteDirection
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseIndex clause).literals = [second, first] := by
  have arity : clause.literals.length = 2 := by simp [literalsEq]
  have firstDirection :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_binary
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember arity
      (literal := first) (literalIndex := 0) (by simp [literalsEq])
  have secondDirection :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_binary
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember arity
      (literal := second) (literalIndex := 1) (by simp [literalsEq])
  simp [PositionedPeriodicCNF.orderClauseByRouteDirection,
    PositionedPeriodicCNF.clauseLiteralOrder,
    PositionedPeriodicCNF.clauseLiteralDirectionLE,
    PositionedPeriodicCNF.clauseLiteralDirectionRank,
    AxisDirection.binaryUnitEliminationClauseExitDirection,
    AxisDirection.clockwiseRank, literalsEq,
    firstDirection, secondDirection]

end PeriodicOrthocrossing
end LeanTrominoes

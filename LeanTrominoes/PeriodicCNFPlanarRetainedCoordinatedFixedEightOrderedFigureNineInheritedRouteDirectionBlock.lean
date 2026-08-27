/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineOwnRouteCompiledDirectionData
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSuffixCases

/-! # Finite blocks for named retained inherited Figure 9 routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

local instance inheritedRouteDirectionBlockVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Every genuine inherited incidence in the named retained route family has
one finite local-plus-connector query followed by factor-`144` repetition of
the corresponding source-route tail word. -/
theorem
    retainedOrderedFixedEightFigureNineInheritedRoute_directionBlock
    {Variable : Type} [DecidableEq Variable]
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    ∃ (data :
        PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex)
        (first second : Cell) (rest : List Cell)
        (query :
          PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery),
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex = some data ∧
        retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex =
          first :: second :: rest ∧
        unitSubdivisionDirections
            (AxisDirection.normalizeOrthogonalPolyline
              (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty clauseIndex literalIndex)) =
          PlanarOneInThreeNoUnitsFigureNine.normalizedLocalExtendedDirectionBlock
              query ++
            repeatDirections 144
              (unitSubdivisionDirections (second :: rest)) := by
  rcases
      retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_fanInheritedRoute_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, dataLookup, rawShape⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem
      data.sourceClauseMember with
    ⟨clockwiseClause, clockwiseClauseMember, sourceClauseEq⟩
  have clockwiseLiteralMember :
      (data.sourceLiteral, data.sourceLiteralIndex) ∈
        clockwiseClause.literals.zipIdx := by
    have scaledLiteralMember := data.sourceLiteralMember
    rw [sourceClauseEq] at scaledLiteralMember
    simpa using scaledLiteralMember
  have sourceRouteLength :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember clockwiseLiteralMember
  cases routeEq :
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source data.sourceClauseIndex data.sourceLiteralIndex with
  | nil => simp [routeEq] at sourceRouteLength
  | cons first tail =>
      cases tail with
      | nil => simp [routeEq] at sourceRouteLength
      | cons second rest =>
          rcases
              retainedOrderedFixedEightFigureNineOwnInheritedRoute_compiledDirectionWord
                source sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty data first second rest routeEq with
            ⟨templateIndex, compiledWord⟩
          let clearanceWidth :=
            retainedFigureNineClearancePositionedFormula_widthAtMostThree
              source sourceWidth
          let fanData :=
            PositionedPeriodicCNF.clauseExitFanData
              data.sourceClause data.sourceClauseIndex
              (retainedFigureNineClearanceIncidenceRoutes source)
          let slot := data.sourceSlot clearanceWidth
          let profile :=
            PeriodicCNF.FormulaShapeOfFormula.clauseProfile
              (PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles
                data.sourceClause.literals)
          let query :
              PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery :=
            ⟨profile, templateIndex, fanData, slot⟩
          have clearanceRouteEq :=
            retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty data.sourceClauseMember
              data.sourceLiteralMember
          have clearanceFactorEq :
              (retainedFigureNineSourceClearanceFactor : Int) = 2 := by
            rfl
          rw [clearanceFactorEq] at clearanceRouteEq
          refine ⟨data, first, second, rest, query,
            dataLookup, routeEq, ?_⟩
          rw [rawShape, clearanceRouteEq, routeEq]
          simpa only [query, profile, fanData, slot, clearanceWidth] using
            compiledWord

end PeriodicOrthocrossing
end LeanTrominoes

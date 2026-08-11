import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrdering
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderingComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineCompleteRouteComputability

/-!
# Computability of the retained final clockwise ordering

This module specializes the proof-free complete Figure 9 route lookup to the
retained fixed-eight source.  It then normalizes those spliced routes and uses
their first directions to compute the second and final clockwise clause sort.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Proof-free complete retained route lookup before final loop erasure. -/
def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  PlanarOneInThreeNoUnitsFigureNine.splicedRoutesComputed
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearanceIncidenceRoutes source)
    clauseIndex literalIndex

theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed
        input.1.1 input.1.2 input.2 := by
  exact
    PlanarOneInThreeNoUnitsFigureNine.splicedRoutesComputed_primrec
      retainedFigureNineClearancePositionedFormula
      retainedFigureNineClearancePlacement
      retainedFigureNineClearanceIncidenceRoutes
      retainedFigureNineClearancePositionedFormula_primrec
      retainedFigureNineClearancePlacement_period_primrec
      retainedFigureNineClearanceIncidenceRoutes_primrec

/-- For every valid source, the proof-free raw route lookup is exactly the
proof-backed geometric route family already used by the drawing. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clauseIndex literalIndex : Nat) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed
        source clauseIndex literalIndex =
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex := by
  apply PlanarOneInThreeNoUnitsFigureNine.splicedRoutesComputed_eq
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedFigureNineClearanceIncidenceRoutes source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
  intro selectedClauseIndex selectedLiteralIndex
  rfl

/-- Proof-free loop erasure of the computed complete retained route. -/
def
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  AxisDirection.normalizeOrthogonalPolyline
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed
      source clauseIndex literalIndex)

theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
        input.1.1 input.1.2 input.2 := by
  exact AxisDirection.normalizeOrthogonalPolyline_primrec.comp
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed_primrec

theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clauseIndex literalIndex : Nat) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
        source clauseIndex literalIndex =
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex := by
  unfold
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutesComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex]

/-- The final clockwise clause presentation computed directly from the
proof-free normalized route lookup. -/
def
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PositionedPeriodicCNF.orderClausesByRouteDirection
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source)
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
      source)

theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed :
        PeriodicCNF Variable → _) := by
  exact PositionedPeriodicCNF.orderClausesByRouteDirection_primrec
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_primrec
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed_primrec

/-- On a valid source, the proof-free final sort is definitionally the same
stable sort as the proof-backed endpoint formula. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
        source =
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty := by
  have routesEq :
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
          source =
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty := by
    funext clauseIndex literalIndex
    exact
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed_eq
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula,
    routesEq]

end PeriodicOrthocrossing
end LeanTrominoes

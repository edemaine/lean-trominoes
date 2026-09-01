/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendRecordFamilyPresentation
import LeanTrominoes.RetainedAngularFanNormalizedClauseBatchedRecordSemantics

/-! # Expanded semantic records of final retained-bend families -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Expanded semantic records of one globally indexed tagged bend. -/
def finalBendSourceClauseRecordsAt
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : (RouteBend × Bool) × Nat) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  let positionedClause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨(0, 0), normalizedBendClauseAt formula tagged.1⟩
  sourceClauseRecords
    (routedCopiedClauseProfile formula tagged.2 positionedClause)
    (orderedTailDirections
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula)
      tagged.2
      (copiedOccurrenceClause formula tagged.2 positionedClause))

/-- Expanded semantic bend records, grouped recursively by physical bend. -/
def finalBendSourceClauseRecordsFrom
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Nat → List RouteBend →
      List HorizontalRoutedRouteHeaderTail.Token
  | _, [] => []
  | start, routeBend :: routeBends =>
      finalBendSourceClauseRecordsAt formula ((routeBend, true), start) ++
        finalBendSourceClauseRecordsAt formula
            ((routeBend, false), start + 1) ++
          finalBendSourceClauseRecordsFrom formula (start + 2) routeBends

/-- Recursive physical-bend grouping is the ordinary clause-major flattening
of the indexed tagged-bend product. -/
theorem finalBendSourceClauseRecordsFrom_eq_product
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBends : List RouteBend)
    (start : Nat) :
    finalBendSourceClauseRecordsFrom formula start routeBends =
      ((routeBends.product [true, false]).zipIdx start).flatMap
        (finalBendSourceClauseRecordsAt formula) := by
  induction routeBends generalizing start with
  | nil => rfl
  | cons routeBend routeBends induction =>
      simp only [finalBendSourceClauseRecordsFrom, List.append_assoc]
      rw [induction (start + 2)]
      congr 1

end PeriodicEightOccurrenceSplit
end LeanTrominoes

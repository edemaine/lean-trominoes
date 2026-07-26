import LeanTrominoes.PeriodicCNFPlanarAngularOneInThreePositioned
import LeanTrominoes.PeriodicCNFPlanarNormalizationDegree
import LeanTrominoes.PeriodicEightOccurrenceSplitOrdered

/-!
# Fixed-eight occurrence splitting after periodic planarization

The normalized planar-SAT degree bound supplies the eight-slot premise for
the concrete angular occurrence order.  This module applies the uniform
Figure 7 implication ring to the deduplicated wrapped planar-SAT formula and
records its degree-three and satisfiability guarantees.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 800000

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight_of_source
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : formula.IsLocal)
    (width : formula.WidthAtMost 3)
    (occurrences : formula.OccurrencesAtMost 3) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).OccurrencesAtMost 8 := by
  have defaultBound :=
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
      (PeriodicCNF.incidenceGraph_isWellFormed formula)
      (PeriodicCNF.incidenceGraph_degreeAtMost width occurrences)
      (PeriodicCNF.incidenceGraph_isLocal isLocal)
      occurrences
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 8
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    defaultBound

def drawingSemanticAngularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    OccurrenceOrder
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula) :=
  @PeriodicThreeSATThree.angularOccurrenceOrder
    (WrappedPeriodicPlanarSATVariable Variable)
    drawingOrderedWrappedPeriodicPlanarSATVariableDecidableEq
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)

theorem drawingSemanticAngularOccurrenceOrder_fitsEightSlots
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : formula.IsLocal)
    (width : formula.WidthAtMost 3)
    (occurrences : formula.OccurrencesAtMost 3) :
    FitsEightSlots
      (drawingSemanticAngularOccurrenceOrder formula) := by
  apply fitsEightSlots_of_occurrencesAtMostEight
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight_of_source
      isLocal width occurrences

def drawingEightOccurrenceSplitFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplit.orderedFormula
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
    (drawingSemanticAngularOccurrenceOrder formula)

theorem drawingEightOccurrenceSplitFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : formula.IsLocal)
    (width : formula.WidthAtMost 3)
    (occurrences : formula.OccurrencesAtMost 3) :
    (drawingEightOccurrenceSplitFormula
      formula).OccurrencesAtMost 3 := by
  apply PeriodicEightOccurrenceSplit.orderedFormula_occurrencesAtMostThree
  exact drawingSemanticAngularOccurrenceOrder_fitsEightSlots
    isLocal width occurrences

theorem drawingEightOccurrenceSplitFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingEightOccurrenceSplitFormula
      formula).Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  exact
    (PeriodicEightOccurrenceSplit.orderedFormula_satisfiable_iff
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
      (drawingSemanticAngularOccurrenceOrder formula)).trans
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
        formula)

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Endpoint-compatible routes for fixed-eight occurrence splitting

This module equips the positioned Figure 7 formula with a canonical
orthogonal route family.  It proves the exact periodic incidence endpoints
and axis alignment needed by later noncrossing ring-splicing refinements.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

def drawingEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.orthogonalIncidenceRoutes
    (drawingEightOccurrenceSplitPositionedFormula formula)
    (drawingEightOccurrenceSplitPlacement formula)

theorem drawingEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 < (drawingEightOccurrenceSplitPlacement formula).period := by
  unfold drawingEightOccurrenceSplitPlacement
  apply PeriodicEightOccurrenceSplitPositioned.placement_period_pos
  exact drawingPeriodicPlanarSATPlacement_period_pos formula

theorem drawingEightOccurrenceSplitIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).RoutesMatch
      (drawingEightOccurrenceSplitPositionedFormula
        formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_routesMatch
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitPlacement_period_pos formula)

theorem drawingEightOccurrenceSplitIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).IsOrthogonal := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_isOrthogonal
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)

end PeriodicOrthocrossing
end LeanTrominoes

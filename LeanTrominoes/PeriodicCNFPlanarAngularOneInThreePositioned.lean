/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOrderedOneInThreePositioned
import LeanTrominoes.PeriodicCNFPlanarSATIncidenceRoutes
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Angularly ordered positioned planar exact-one source

The routed SAT incidences determine a concrete polar-angle order before
high-degree variables are split.  This file specializes the parameterized
ordered reduction to that order and packages the final positioned, unit-free
exact-one formula consumed by the planar 3DM construction.

This layer is semantic and positional.  The subsequent drawing layer must
route the split occurrence cycles and the two local exact-one replacements
orthogonally and prove continuous planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- The same terminal-ray sort as `drawingAngularOccurrenceOrder`, rebuilt
under the opaque wrapped-variable equality instance used by the ordered
pipeline.  `OccurrenceOrder` retains that implementation as an implicit
parameter, so this bridge makes the instance choice explicit. -/
def drawingOrderedAngularOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingOccurrenceOrder formula :=
  @PeriodicThreeSATThree.angularOccurrenceOrder
    (WrappedPeriodicPlanarSATVariable Variable)
    drawingOrderedWrappedPeriodicPlanarSATVariableDecidableEq
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
    (deduplicatedWrappedDrawingPeriodicPlanarSATStraightIncidenceRoutes
      formula)

/-- Routed planar SAT after occurrence splitting in terminal-ray angular
order. -/
def drawingAngularPositionedPeriodicPlanarThreeSATThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
    formula (drawingOrderedAngularOccurrenceOrder formula)

/-- Placement paired with angularly ordered occurrence splitting. -/
def drawingAngularPeriodicPlanarThreeSATThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  drawingOrderedPeriodicPlanarThreeSATThreePlacement
    formula (drawingOrderedAngularOccurrenceOrder formula)

/-- Final positioned unit-free exact-one formula in the concrete angular
order. -/
def drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    formula (drawingOrderedAngularOccurrenceOrder formula)

/-- Placement paired with the concrete angular unit-free exact-one source. -/
def drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  drawingOrderedPeriodicPlanarOneInThreeNoUnitsPlacement
    formula (drawingOrderedAngularOccurrenceOrder formula)

/-- Angular occurrence splitting gives the degree promise required by the
planar 3DM variable gadgets. -/
theorem
    drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula).erase.OccurrencesAtMost 3 := by
  exact
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
      formula (drawingOrderedAngularOccurrenceOrder formula) sourceWidth

/-- Every clause in the concrete angular exact-one source has arity two or
three. -/
theorem
    drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula).erase := by
  exact
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
      formula (drawingOrderedAngularOccurrenceOrder formula)

/-- The concrete positioned exact-one source is satisfiable exactly when the
input periodic CNF is satisfiable. -/
theorem
    drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          formula).erase ↔
      formula.Satisfiable := by
  exact
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
      formula (drawingOrderedAngularOccurrenceOrder formula)
      sourceWidth sourceOccurrences

/-- All refinement stages retain a positive physical drawing period. -/
theorem drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 <
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement
        formula).period := by
  unfold
    drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement
    drawingOrderedPeriodicPlanarOneInThreeNoUnitsPlacement
  apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
  unfold drawingOrderedPeriodicPlanarOneInThreeThreePlacement
  change
    0 <
      (drawingOrderedPeriodicPlanarOneInThreeThreeRawPlacement
        formula (drawingOrderedAngularOccurrenceOrder formula)).period
  unfold drawingOrderedPeriodicPlanarOneInThreeThreeRawPlacement
  apply PeriodicOneInThreePositioned.placement_period_pos
  unfold drawingOrderedPeriodicPlanarThreeSATThreePlacement
  apply PeriodicThreeSATThreePositioned.orderedPlacement_period_pos
  change 0 < (drawingPeriodicPlanarSATPlacement formula).period
  exact drawingPeriodicPlanarSATPlacement_period_pos formula

/-- Canonical orthogonal detours for the concrete angular exact-one source. -/
def drawingAngularPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.orthogonalIncidenceRoutes
    (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula)
    (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement formula)

/-- The concrete angular exact-one detours have exact periodic incidence
endpoints. -/
theorem
    drawingAngularPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        formula)).RoutesMatch
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_routesMatch
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
        formula)

/-- Every segment in the concrete angular exact-one detour drawing is
axis-aligned. -/
theorem
    drawingAngularPeriodicPlanarOneInThreeNoUnitsIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        formula)).IsOrthogonal := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_isOrthogonal
      (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula)
      (drawingAngularPeriodicPlanarOneInThreeNoUnitsPlacement formula)

end PeriodicOrthocrossing
end LeanTrominoes

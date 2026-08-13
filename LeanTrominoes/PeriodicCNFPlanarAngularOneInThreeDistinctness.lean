/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarAngularOneInThreePositioned
import LeanTrominoes.PlanarOneInThreeLocalDistinctness

/-!
# Clause-atom distinctness in the angular exact-one source

Figure 9 gives every generated clause distinct atoms, injective opaque
wrapping preserves that property, and unit elimination preserves it again.
This file packages those facts for both the parameterized ordered pipeline
and its concrete angular specialization used by the hardness construction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The raw positioned Figure 9 output has distinct atoms in every clause. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
      formula order).AllAtomsNodup := by
  exact PeriodicOneInThreePositioned.formula_allAtomsNodup
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
      formula order)

/-- Opaque wrapping preserves the positioned Figure 9 distinctness
certificate. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
      formula order).AllAtomsNodup := by
  apply PositionedPeriodicCNF.allAtomsNodup_rename
    WrappedPeriodicVariable.mk
  · intro first second equal
    exact WrappedPeriodicVariable.mk.inj equal
  · exact
      drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_allAtomsNodup
        formula order

/-- The final ordered, unit-free exact-one source has distinct atoms in every
binary or ternary clause. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula order).AllAtomsNodup := by
  exact PeriodicOneInThreeNoUnitsPositioned.formula_allAtomsNodup
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
      formula order)
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula_allAtomsNodup
      formula order)

/-- Concrete angular specialization of the final clause-atom distinctness
certificate. -/
theorem
    drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingAngularPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula).AllAtomsNodup := by
  exact
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
      formula (drawingOrderedAngularOccurrenceOrder formula)

end PeriodicOrthocrossing
end LeanTrominoes

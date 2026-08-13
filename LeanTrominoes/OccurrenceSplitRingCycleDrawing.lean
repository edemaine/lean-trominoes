/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplit
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Certified separator implication-cycle subdrawing of Figure 7

The full fixed-eight drawing contains both the eight retained old incidences
and the implication ring.  Route splicing needs the latter as an independently
indexed local template, because copied source incidences are supplied by the
surrounding planar drawing.

This module packages exactly the nine implication clauses (including the
degree-two separator) and their eighteen direct incidence routes.
Exhaustive verification proves exact
endpoints, orthogonality, and continuous planarity.  Its final theorem
identifies the embedded local clauses definitionally with the semantic
eight-port implication cycle after renaming ring vertices to copies.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT

/-- The implication ring as a standalone finite incidence drawing. -/
def cycleDrawing : EmbeddedCNFIncidenceDrawing RingVertex where
  formula := cycleFormula
  variablePosition := ringVariablePosition
  routes := cycleRoutes

/-- The standalone implication ring has exact endpoints, orthogonal routes,
and continuous planarity. -/
theorem cycleDrawing_isValid : cycleDrawing.IsValid := by
  native_decide

theorem cycleDrawing_routesMatch : cycleDrawing.RoutesMatch :=
  cycleDrawing_isValid.1

theorem cycleDrawing_isOrthogonal : cycleDrawing.IsOrthogonal :=
  cycleDrawing_isValid.2.1

theorem cycleDrawing_isPlanar : cycleDrawing.IsPlanar :=
  cycleDrawing_isValid.2.2

/-- One implication ring placed at an arbitrary macrocell origin. -/
def translatedCycleDrawing (offset : Cell) :
    EmbeddedCNFIncidenceDrawing RingVertex :=
  cycleDrawing.translate offset

/-- Every translated implication ring inherits the complete local
certificate. -/
theorem translatedCycleDrawing_isValid (offset : Cell) :
    (translatedCycleDrawing offset).IsValid :=
  EmbeddedCNFIncidenceDrawing.isValid_translate
    cycleDrawing_isValid offset

/-- Rename one local implication clause to the eight source-port copies or
the separator copy of a source atom, and add the common zero offset. -/
def periodicCycleClause
    {Variable : Type*} (atom : Variable)
    (clause : EmbeddedClause RingVertex) :
    PeriodicClause (ThreeOccurrenceVariable Variable) :=
  clause.literals.map fun literal =>
    ⟨PeriodicEightOccurrenceSplit.ringCopy atom literal.1,
      (0, 0), literal.2⟩

/-- The semantic separator implication cycle is exactly the erased local
cycle template in its separator-cut presentation. -/
theorem cycleClausesFor_eq_cycleFormula
    {Variable : Type*} (atom : Variable) :
    PeriodicEightOccurrenceSplit.cycleClausesFor atom =
      cycleFormula.map (periodicCycleClause atom) := by
  rfl

end OccurrenceSplitRing
end LeanTrominoes

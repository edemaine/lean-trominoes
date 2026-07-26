import LeanTrominoes.PeriodicEightOccurrenceSplit

/-!
# Certified implication-cycle subdrawing of Figure 7

The full fixed-eight drawing contains both the eight retained old incidences
and the implication ring.  Route splicing needs the latter as an independently
indexed local template, because copied source incidences are supplied by the
surrounding planar drawing.

This module packages exactly those eight implication clauses and their
sixteen direct incidence routes.  Exhaustive verification proves exact
endpoints, orthogonality, and continuous planarity.  Its final theorem
identifies the embedded local clauses definitionally with the semantic
fixed-eight implication cycle after renaming ports to copies.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT

/-- The eight implication clauses, without the retained old incidences. -/
def cycleFormula : List (EmbeddedClause Port) :=
  ports.map cycleClause

/-- Presentation-indexed incidence routes for the implication cycle. -/
def cycleRoutes
    (clauseIndex literalIndex : Nat) : List Cell :=
  if clauseIndex < ports.length then
    cycleRoute
      (ports.getD clauseIndex .northwest) literalIndex
  else
    []

/-- The implication ring as a standalone finite incidence drawing. -/
def cycleDrawing : EmbeddedCNFIncidenceDrawing Port where
  formula := cycleFormula
  variablePosition := variablePosition
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

/-- Rename one local implication clause to the eight fixed copies of a
source atom and add the common zero periodic offset. -/
def periodicCycleClause
    {Variable : Type*} (atom : Variable)
    (clause : EmbeddedClause Port) :
    PeriodicClause (ThreeOccurrenceVariable Variable) :=
  clause.literals.map fun literal =>
    ⟨PeriodicEightOccurrenceSplit.copy atom literal.1,
      (0, 0), literal.2⟩

/-- The semantic fixed-eight implication cycle is exactly the erased local
cycle template. -/
theorem cycleClausesFor_eq_cycleFormula
    {Variable : Type*} (atom : Variable) :
    PeriodicEightOccurrenceSplit.cycleClausesFor atom =
      cycleFormula.map (periodicCycleClause atom) := by
  rfl

end OccurrenceSplitRing
end LeanTrominoes

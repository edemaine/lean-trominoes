import LeanTrominoes.PeriodicCNFPlanarVertexGadgets

/-!
# Combined routed planar SAT formula

This file places the complete crossover/route core and the clause/variable
vertex families under one variable type.  It proves an exact componentwise
satisfaction theorem and a simultaneous extension theorem for any compatible
route and central-atom assignments.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Variables of the combined finite planarized formula.  The left summand
contains every external carrier or central atom node; the right summand
contains crossover-site-scoped internal variables. -/
abbrev PlanarSATVariable (Variable : Type*) :=
  Sum (PlanarSATNode Variable)
    (CrossingRecord × CrossoverInternal)

/-- Embed the complete route core's variables into the combined planar SAT
variable type. -/
def planarSATCoreVariableMap {Variable : Type*} :
    Sum CarrierNode (CrossingRecord × CrossoverInternal) →
      PlanarSATVariable Variable
  | .inl node => .inl (.carrier node)
  | .inr internal => .inr internal

/-- Embed an external clause/variable-gadget node into the combined type. -/
def planarSATExternalVariableMap {Variable : Type*} :
    PlanarSATNode Variable → PlanarSATVariable Variable :=
  Sum.inl

/-- The complete route core for the incidence graph, renamed into the
combined planar SAT variable type. -/
def scopedDrawingPlanarSATCore
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (drawingRoutePlanarCoreFormula
    (PeriodicCNF.incidenceGraph formula)).map fun clause =>
      clause.rename planarSATCoreVariableMap

/-- Routed original clauses, renamed into the external summand. -/
def scopedDrawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (drawingRoutedClauseFormula formula).map fun clause =>
    clause.rename planarSATExternalVariableMap

/-- Routed variable duplicators, renamed into the external summand. -/
def scopedDrawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (drawingRoutedVariableFormula formula).map fun clause =>
    clause.rename planarSATExternalVariableMap

@[simp]
theorem scopedDrawingPlanarSATCore_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment (scopedDrawingPlanarSATCore formula) ↔
      FormulaHolds (assignment ∘ planarSATCoreVariableMap)
        (drawingRoutePlanarCoreFormula
          (PeriodicCNF.incidenceGraph formula)) := by
  exact formulaHolds_map assignment planarSATCoreVariableMap id
    (drawingRoutePlanarCoreFormula
      (PeriodicCNF.incidenceGraph formula))

@[simp]
theorem scopedDrawingRoutedClauseFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment
        (scopedDrawingRoutedClauseFormula formula) ↔
      FormulaHolds (assignment ∘ planarSATExternalVariableMap)
        (drawingRoutedClauseFormula formula) := by
  exact formulaHolds_map assignment planarSATExternalVariableMap id
    (drawingRoutedClauseFormula formula)

@[simp]
theorem scopedDrawingRoutedVariableFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment
        (scopedDrawingRoutedVariableFormula formula) ↔
      FormulaHolds (assignment ∘ planarSATExternalVariableMap)
        (drawingRoutedVariableFormula formula) := by
  exact formulaHolds_map assignment planarSATExternalVariableMap id
    (drawingRoutedVariableFormula formula)

/-- All crossover, complete-route, original-clause, and variable-duplicator
clauses in the neighboring finite drawing block. -/
def drawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  scopedDrawingPlanarSATCore formula ++
    scopedDrawingRoutedClauseFormula formula ++
    scopedDrawingRoutedVariableFormula formula

/-- Satisfaction of the combined formula is exactly satisfaction of its
route core, routed clauses, and routed variable duplicators. -/
theorem drawingPlanarSATFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment (drawingPlanarSATFormula formula) ↔
      FormulaHolds (assignment ∘ planarSATCoreVariableMap)
          (drawingRoutePlanarCoreFormula
            (PeriodicCNF.incidenceGraph formula)) ∧
        FormulaHolds (assignment ∘ planarSATExternalVariableMap)
            (drawingRoutedClauseFormula formula) ∧
          FormulaHolds (assignment ∘ planarSATExternalVariableMap)
            (drawingRoutedVariableFormula formula) := by
  rw [drawingPlanarSATFormula,
    formulaHolds_route_append_iff,
    formulaHolds_route_append_iff,
    scopedDrawingPlanarSATCore_holds_iff,
    scopedDrawingRoutedClauseFormula_holds_iff,
    scopedDrawingRoutedVariableFormula_holds_iff,
    and_assoc]

/-- Pull a route assignment and a central-atom assignment back to every
external planar SAT node. -/
def routedPlanarSATExternalAssignment
    {Variable : Type*}
    (routeAssignment : RouteOccurrenceKey → Bool)
    (atomAssignment : VariableRouteSite Variable → Bool) :
    PlanarSATNode Variable → Bool
  | .carrier node => routeAssignment node.routeKey
  | .atom occurrence => atomAssignment occurrence

/-- Compatible routed clauses and variable duplicators extend simultaneously
through every complete route and every fresh crossover internal. -/
theorem exists_drawingPlanarSATFormula_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeAssignment : RouteOccurrenceKey → Bool)
    (atomAssignment : VariableRouteSite Variable → Bool)
    (clausesHold :
      FormulaHolds
        (routedPlanarSATExternalAssignment
          routeAssignment atomAssignment)
        (drawingRoutedClauseFormula formula))
    (variablesHold :
      FormulaHolds
        (routedPlanarSATExternalAssignment
          routeAssignment atomAssignment)
        (drawingRoutedVariableFormula formula)) :
    ∃ assignment : PlanarSATVariable Variable → Bool,
      FormulaHolds assignment (drawingPlanarSATFormula formula) ∧
        ∀ node,
          assignment (.inl node) =
            routedPlanarSATExternalAssignment
              routeAssignment atomAssignment node := by
  let graph := PeriodicCNF.incidenceGraph formula
  rcases
      exists_drawingRoutePlanarCoreFormula_holds_of_routeAssignment
        graph routeAssignment with
    ⟨coreAssignment, coreHolds, coreExternal⟩
  let assignment : PlanarSATVariable Variable → Bool
    | .inl (.carrier node) => coreAssignment (.inl node)
    | .inl (.atom occurrence) => atomAssignment occurrence
    | .inr internal => coreAssignment (.inr internal)
  have coreRestriction :
      assignment ∘ planarSATCoreVariableMap = coreAssignment := by
    funext inputVariable
    cases inputVariable <;> rfl
  have externalRestriction :
      assignment ∘ planarSATExternalVariableMap =
        routedPlanarSATExternalAssignment
          routeAssignment atomAssignment := by
    funext node
    cases node with
    | carrier carrierNode =>
        exact coreExternal carrierNode
    | atom occurrence =>
        rfl
  refine ⟨assignment,
    (drawingPlanarSATFormula_holds_iff formula assignment).mpr
      ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [coreRestriction]
    exact coreHolds
  · rw [externalRestriction]
    exact clausesHold
  · rw [externalRestriction]
    exact variablesHold
  · intro node
    have restricted :=
      congrFun externalRestriction node
    exact restricted

end PeriodicOrthocrossing
end LeanTrominoes

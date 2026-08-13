/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarFormula
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-!
# Planar SAT formula with retained carrier representatives

The original finite routed formula uses the canonical carrier chains as a
semantic presentation.  A canonical carrier link can, however, pass through
a translated crossover belonging to another periodic copy.  The retained
carrier family splits every such physical corridor at all relevant
crossovers and chooses one owner for each periodic link orbit.

This file replaces only the straight-carrier part of the finite formula.
Crossover, bend, routed-clause, and routed-variable components are unchanged.
The resulting formula has the same direct completeness interface: one value
per translated route occurrence satisfies every retained wire and extends
through the crossover gadgets.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Retained straight-carrier clauses followed by the unchanged bend
equalities. -/
def retainedDrawingRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause CarrierNode) :=
  retainedDrawingCompleteCarrierFormula graph ++
    drawingRouteBendFormula graph

/-- A single value per translated route occurrence satisfies the retained
straight carriers and all bend links. -/
theorem retainedDrawingRouteWireFormula_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment : RouteOccurrenceKey → Bool) :
    FormulaHolds (assignment ∘ CarrierNode.routeKey)
      (retainedDrawingRouteWireFormula graph) := by
  rw [retainedDrawingRouteWireFormula,
    formulaHolds_route_append_iff]
  constructor
  · simpa [CarrierNode.routeKey, SegmentTerminal.routeKey,
      segmentCarrierRouteKey, Function.comp_def] using
      retainedDrawingCompleteCarrierFormula_holds graph
        (assignment ∘ segmentCarrierRouteKey)
  · exact drawingRouteBendFormula_holds graph assignment

/-- Scope every retained route-wire variable into the external summand used
by the crossover family. -/
def retainedScopedDrawingRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))) :=
  (retainedDrawingRouteWireFormula graph).map fun clause =>
    clause.rename fun node =>
      (Sum.inl node :
        Sum CarrierNode (CrossingRecord × CrossoverInternal))

@[simp]
theorem retainedScopedDrawingRouteWireFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment
        (retainedScopedDrawingRouteWireFormula graph) ↔
      FormulaHolds (assignment ∘ Sum.inl)
        (retainedDrawingRouteWireFormula graph) := by
  exact formulaHolds_map assignment
    (fun node =>
      (Sum.inl node :
        Sum CarrierNode (CrossingRecord × CrossoverInternal)))
    id (retainedDrawingRouteWireFormula graph)

/-- The retained local route core: the unchanged crossover family together
with retained straight carriers and the unchanged bend equalities. -/
def retainedDrawingRoutePlanarCoreFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))) :=
  drawingCarrierNodeCrossoverFormula graph ++
    retainedScopedDrawingRouteWireFormula graph

/-- Satisfaction of the retained route core splits into its crossover and
retained-wire components. -/
theorem retainedDrawingRoutePlanarCoreFormula_holds_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool) :
    FormulaHolds assignment
        (retainedDrawingRoutePlanarCoreFormula graph) ↔
      FormulaHolds assignment
          (drawingCarrierNodeCrossoverFormula graph) ∧
        FormulaHolds (assignment ∘ Sum.inl)
          (retainedDrawingRouteWireFormula graph) := by
  rw [retainedDrawingRoutePlanarCoreFormula,
    formulaHolds_route_append_iff,
    retainedScopedDrawingRouteWireFormula_holds_iff]

/-- The canonical route-signal assignment satisfies the retained route core.
Only the wire proof changes; the crossover truth-table assignment is reused
verbatim from the canonical core. -/
theorem canonicalRoutePlanarCoreAssignment_retained_holds
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeAssignment : RouteOccurrenceKey → Bool) :
    FormulaHolds
      (canonicalRoutePlanarCoreAssignment routeAssignment)
      (retainedDrawingRoutePlanarCoreFormula graph) := by
  apply
    (retainedDrawingRoutePlanarCoreFormula_holds_iff
      graph
      (canonicalRoutePlanarCoreAssignment routeAssignment)).mpr
  constructor
  · exact
      (drawingRoutePlanarCoreFormula_holds_iff
        graph
        (canonicalRoutePlanarCoreAssignment routeAssignment)).mp
          (canonicalRoutePlanarCoreAssignment_holds
            graph routeAssignment) |>.1
  · have restriction :
        canonicalRoutePlanarCoreAssignment routeAssignment ∘ Sum.inl =
          routeAssignment ∘ CarrierNode.routeKey := by
      funext node
      rfl
    rw [restriction]
    exact retainedDrawingRouteWireFormula_holds
      graph routeAssignment

/-- Embed the retained route core into the combined planar-SAT variable
type. -/
def retainedScopedDrawingPlanarSATCore
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  (retainedDrawingRoutePlanarCoreFormula
    (PeriodicCNF.incidenceGraph formula)).map fun clause =>
      clause.rename planarSATCoreVariableMap

@[simp]
theorem retainedScopedDrawingPlanarSATCore_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment
        (retainedScopedDrawingPlanarSATCore formula) ↔
      FormulaHolds (assignment ∘ planarSATCoreVariableMap)
        (retainedDrawingRoutePlanarCoreFormula
          (PeriodicCNF.incidenceGraph formula)) := by
  exact formulaHolds_map assignment planarSATCoreVariableMap id
    (retainedDrawingRoutePlanarCoreFormula
      (PeriodicCNF.incidenceGraph formula))

/-- The finite routed planar-SAT formula using the retained carrier
representatives. -/
def retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  retainedScopedDrawingPlanarSATCore formula ++
    scopedDrawingRoutedClauseFormula formula ++
    scopedDrawingRoutedVariableFormula formula

/-- Satisfaction of the retained combined formula is exactly satisfaction
of its retained route core, routed clauses, and routed variable
duplicators. -/
theorem retainedDrawingPlanarSATFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATVariable Variable → Bool) :
    FormulaHolds assignment
        (retainedDrawingPlanarSATFormula formula) ↔
      FormulaHolds (assignment ∘ planarSATCoreVariableMap)
          (retainedDrawingRoutePlanarCoreFormula
            (PeriodicCNF.incidenceGraph formula)) ∧
        FormulaHolds (assignment ∘ planarSATExternalVariableMap)
            (drawingRoutedClauseFormula formula) ∧
          FormulaHolds (assignment ∘ planarSATExternalVariableMap)
            (drawingRoutedVariableFormula formula) := by
  rw [retainedDrawingPlanarSATFormula,
    formulaHolds_route_append_iff,
    formulaHolds_route_append_iff,
    retainedScopedDrawingPlanarSATCore_holds_iff,
    scopedDrawingRoutedClauseFormula_holds_iff,
    scopedDrawingRoutedVariableFormula_holds_iff,
    and_assoc]

/-- Compatible routed clauses and variable duplicators extend
simultaneously through every retained route wire and crossover internal. -/
theorem exists_retainedDrawingPlanarSATFormula_holds
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
      FormulaHolds assignment
          (retainedDrawingPlanarSATFormula formula) ∧
        ∀ node,
          assignment (.inl node) =
            routedPlanarSATExternalAssignment
              routeAssignment atomAssignment node := by
  let coreAssignment :=
    canonicalRoutePlanarCoreAssignment routeAssignment
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
    cases node <;> rfl
  refine
    ⟨assignment,
      (retainedDrawingPlanarSATFormula_holds_iff
        formula assignment).mpr ⟨?_, ?_, ?_⟩,
      ?_⟩
  · rw [coreRestriction]
    exact canonicalRoutePlanarCoreAssignment_retained_holds
      (PeriodicCNF.incidenceGraph formula) routeAssignment
  · rw [externalRestriction]
    exact clausesHold
  · rw [externalRestriction]
    exact variablesHold
  · intro node
    exact congrFun externalRestriction node

end PeriodicOrthocrossing
end LeanTrominoes

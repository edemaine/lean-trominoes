/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedFormula
import LeanTrominoes.PlanarThreeSATOccurrenceRenaming

/-! # Exact occurrence blocks of the retained planar-SAT formula -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Scoping the retained route core maps its occurrence list by the core
variable embedding. -/
@[simp] theorem embeddedVariableOccurrences_retainedScopedDrawingPlanarSATCore
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    embeddedVariableOccurrences
        (retainedScopedDrawingPlanarSATCore formula) =
      (embeddedVariableOccurrences
        (retainedDrawingRoutePlanarCoreFormula
          (PeriodicCNF.incidenceGraph formula))).map
        planarSATCoreVariableMap := by
  rw [retainedScopedDrawingPlanarSATCore,
    embeddedVariableOccurrences_rename]

/-- Scoping the routed-variable block maps its occurrence list by the external
variable embedding. -/
@[simp] theorem embeddedVariableOccurrences_scopedDrawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    embeddedVariableOccurrences
        (scopedDrawingRoutedVariableFormula formula) =
      (embeddedVariableOccurrences
        (drawingRoutedVariableFormula formula)).map
          planarSATExternalVariableMap := by
  rw [scopedDrawingRoutedVariableFormula,
    embeddedVariableOccurrences_rename]

/-- Scoping the routed-clause block maps its occurrence list by the external
variable embedding. -/
@[simp] theorem embeddedVariableOccurrences_scopedDrawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    embeddedVariableOccurrences
        (scopedDrawingRoutedClauseFormula formula) =
      (embeddedVariableOccurrences
        (drawingRoutedClauseFormula formula)).map
          planarSATExternalVariableMap := by
  rw [scopedDrawingRoutedClauseFormula,
    embeddedVariableOccurrences_rename]

/-- The retained planar-SAT occurrence list is the concatenation of its core,
routed-clause, and routed-variable occurrence blocks. -/
theorem embeddedVariableOccurrences_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) =
      (embeddedVariableOccurrences
          (retainedScopedDrawingPlanarSATCore formula) ++
        embeddedVariableOccurrences
          (scopedDrawingRoutedClauseFormula formula)) ++
        embeddedVariableOccurrences
          (scopedDrawingRoutedVariableFormula formula) := by
  rw [retainedDrawingPlanarSATFormula,
    embeddedVariableOccurrences_append,
    embeddedVariableOccurrences_append]

/-- Every retained route-core occurrence remains present after embedding the
core and appending the routed clause and variable blocks. -/
theorem retainedDrawingPlanarSATFormula_core_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {atom : Sum CarrierNode (CrossingRecord × CrossoverInternal)}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (retainedDrawingRoutePlanarCoreFormula
        (PeriodicCNF.incidenceGraph formula))) :
    planarSATCoreVariableMap atom ∈ embeddedVariableOccurrences
      (retainedDrawingPlanarSATFormula formula) := by
  rw [embeddedVariableOccurrences_retainedDrawingPlanarSATFormula]
  apply List.mem_append_left
  apply List.mem_append_left
  rw [embeddedVariableOccurrences_retainedScopedDrawingPlanarSATCore]
  exact List.mem_map.mpr ⟨atom, atomMem, rfl⟩

/-- Every routed-variable occurrence remains present after scoping that block
and appending it to the retained planar-SAT formula. -/
theorem retainedDrawingPlanarSATFormula_routedVariable_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {atom : PlanarSATNode Variable}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula)) :
    planarSATExternalVariableMap atom ∈ embeddedVariableOccurrences
      (retainedDrawingPlanarSATFormula formula) := by
  rw [embeddedVariableOccurrences_retainedDrawingPlanarSATFormula]
  apply List.mem_append_right
  rw [embeddedVariableOccurrences_scopedDrawingRoutedVariableFormula]
  exact List.mem_map.mpr ⟨atom, atomMem, rfl⟩

/-- Every routed-clause occurrence remains present after scoping that block
and appending the routed-variable suffix. -/
theorem retainedDrawingPlanarSATFormula_routedClause_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {atom : PlanarSATNode Variable}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (drawingRoutedClauseFormula formula)) :
    planarSATExternalVariableMap atom ∈ embeddedVariableOccurrences
      (retainedDrawingPlanarSATFormula formula) := by
  rw [embeddedVariableOccurrences_retainedDrawingPlanarSATFormula]
  apply List.mem_append_left
  apply List.mem_append_right
  rw [embeddedVariableOccurrences_scopedDrawingRoutedClauseFormula]
  exact List.mem_map.mpr ⟨atom, atomMem, rfl⟩

/-- A routed central-atom occurrence embeds as that exact finite planar-SAT
atom in the retained formula. -/
theorem retainedDrawingPlanarSATFormula_atom_routedVariable_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : VariableRouteSite Variable)
    (atomMem : PlanarSATNode.atom site ∈ embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula)) :
    (Sum.inl (PlanarSATNode.atom site) : PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATExternalVariableMap (PlanarSATNode.atom site) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_routedVariable_occurrence
    formula atomMem

/-- A routed-clause carrier terminal embeds as that exact finite planar-SAT
terminal in the retained formula. -/
theorem retainedDrawingPlanarSATFormula_terminal_routedClause_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (terminal : SegmentTerminal)
    (atomMem : PlanarSATNode.carrier (.terminal terminal) ∈
      embeddedVariableOccurrences (drawingRoutedClauseFormula formula)) :
    (Sum.inl (PlanarSATNode.carrier (.terminal terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATExternalVariableMap
      (PlanarSATNode.carrier (.terminal terminal)) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_routedClause_occurrence
    formula atomMem

/-- A routed-variable carrier terminal embeds as that exact finite planar-SAT
terminal in the retained formula. -/
theorem retainedDrawingPlanarSATFormula_terminal_routedVariable_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (terminal : SegmentTerminal)
    (atomMem : PlanarSATNode.carrier (.terminal terminal) ∈
      embeddedVariableOccurrences (drawingRoutedVariableFormula formula)) :
    (Sum.inl (PlanarSATNode.carrier (.terminal terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATExternalVariableMap
      (PlanarSATNode.carrier (.terminal terminal)) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_routedVariable_occurrence
    formula atomMem

/-- Every crossover-family occurrence remains present after appending the
retained route-wire formula. -/
theorem retainedDrawingRoutePlanarCoreFormula_crossover_occurrence
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {atom : Sum CarrierNode (CrossingRecord × CrossoverInternal)}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (drawingCarrierNodeCrossoverFormula graph)) :
    atom ∈ embeddedVariableOccurrences
      (retainedDrawingRoutePlanarCoreFormula graph) := by
  rw [retainedDrawingRoutePlanarCoreFormula,
    embeddedVariableOccurrences_append]
  exact List.mem_append_left _ atomMem

/-- Scoping the retained route-wire block maps its occurrence list into the
external summand of the route core. -/
@[simp] theorem embeddedVariableOccurrences_retainedScopedDrawingRouteWireFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    embeddedVariableOccurrences
        (retainedScopedDrawingRouteWireFormula graph) =
      (embeddedVariableOccurrences
        (retainedDrawingRouteWireFormula graph)).map Sum.inl := by
  rw [retainedScopedDrawingRouteWireFormula,
    embeddedVariableOccurrences_rename]

/-- Every bend-formula occurrence remains present after prepending the
retained straight-carrier formula. -/
theorem retainedDrawingRouteWireFormula_bend_occurrence
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) {atom : CarrierNode}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (drawingRouteBendFormula graph)) :
    atom ∈ embeddedVariableOccurrences
      (retainedDrawingRouteWireFormula graph) := by
  rw [retainedDrawingRouteWireFormula,
    embeddedVariableOccurrences_append]
  exact List.mem_append_right _ atomMem

/-- Every retained route-wire occurrence remains present after scoping the
wire block and appending it to the crossover family. -/
theorem retainedDrawingRoutePlanarCoreFormula_wire_occurrence
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) {atom : CarrierNode}
    (atomMem : atom ∈ embeddedVariableOccurrences
      (retainedDrawingRouteWireFormula graph)) :
    (Sum.inl atom : Sum CarrierNode
      (CrossingRecord × CrossoverInternal)) ∈
        embeddedVariableOccurrences
          (retainedDrawingRoutePlanarCoreFormula graph) := by
  rw [retainedDrawingRoutePlanarCoreFormula,
    embeddedVariableOccurrences_append]
  apply List.mem_append_right
  rw [embeddedVariableOccurrences_retainedScopedDrawingRouteWireFormula]
  exact List.mem_map.mpr ⟨atom, atomMem, rfl⟩

/-- A bend-terminal occurrence embeds as that exact finite planar-SAT carrier
terminal in the retained formula. -/
theorem retainedDrawingPlanarSATFormula_terminal_bend_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (terminal : SegmentTerminal)
    (atomMem : CarrierNode.terminal terminal ∈
      embeddedVariableOccurrences
        (drawingRouteBendFormula
          (PeriodicCNF.incidenceGraph formula))) :
    (Sum.inl (PlanarSATNode.carrier (.terminal terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATCoreVariableMap
      (Sum.inl (CarrierNode.terminal terminal)) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_core_occurrence formula
    (retainedDrawingRoutePlanarCoreFormula_wire_occurrence
      (PeriodicCNF.incidenceGraph formula)
      (retainedDrawingRouteWireFormula_bend_occurrence
        (PeriodicCNF.incidenceGraph formula) atomMem))

/-- A crossover-internal occurrence in the crossover-family block embeds as
that exact internal variable in the retained planar-SAT formula. -/
theorem retainedDrawingPlanarSATFormula_crossoverInternal_core_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) (internal : CrossoverInternal)
    (atomMem :
      (Sum.inr (crossing, internal) :
          Sum CarrierNode (CrossingRecord × CrossoverInternal)) ∈
        embeddedVariableOccurrences
          (drawingCarrierNodeCrossoverFormula
            (PeriodicCNF.incidenceGraph formula))) :
    (Sum.inr (crossing, internal) : PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATCoreVariableMap (Sum.inr (crossing, internal)) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_core_occurrence formula
    (retainedDrawingRoutePlanarCoreFormula_crossover_occurrence
      (PeriodicCNF.incidenceGraph formula) atomMem)

/-- A boundary occurrence in the crossover-family block embeds as that exact
finite planar-SAT carrier boundary in the retained formula. -/
theorem retainedDrawingPlanarSATFormula_boundary_crossover_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (boundary : CrossingBoundary)
    (atomMem :
      (Sum.inl (CarrierNode.boundary boundary) :
          Sum CarrierNode (CrossingRecord × CrossoverInternal)) ∈
        embeddedVariableOccurrences
          (drawingCarrierNodeCrossoverFormula
            (PeriodicCNF.incidenceGraph formula))) :
    (Sum.inl (PlanarSATNode.carrier (.boundary boundary)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  change planarSATCoreVariableMap
      (Sum.inl (CarrierNode.boundary boundary)) ∈
    embeddedVariableOccurrences (retainedDrawingPlanarSATFormula formula)
  exact retainedDrawingPlanarSATFormula_core_occurrence formula
    (retainedDrawingRoutePlanarCoreFormula_crossover_occurrence
      (PeriodicCNF.incidenceGraph formula) atomMem)

end LeanTrominoes.PeriodicOrthocrossing

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

end LeanTrominoes.PeriodicOrthocrossing

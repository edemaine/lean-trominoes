/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedBoundaryOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATOccurrences

/-! # Periodic occurrences of canonical crossing boundaries -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every canonical drawing boundary survives periodicization as the same
boundary protovariable. -/
theorem boundary_mem_retainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries
      (PeriodicCNF.incidenceGraph formula)) :
    PeriodicPlanarSATVariable.boundary boundary ∈
      (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  rw [retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_eq_map]
  apply List.mem_map.mpr
  refine
    ⟨Sum.inl (PlanarSATNode.carrier (.boundary boundary)),
      boundary_mem_retainedDrawingPlanarSATFormula formula boundaryMem,
      ?_⟩
  simp only [normalizePlanarSATVariable]
  rw [drawingCrossingBoundary_periodNormalize_eq_self
    (PeriodicCNF.incidenceGraph formula) boundaryMem]

end LeanTrominoes.PeriodicOrthocrossing

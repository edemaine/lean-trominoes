/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossoverInternalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATOccurrences

/-! # Periodicization of retained crossover-internal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every canonical crossing internal survives periodicization as the same
periodic protovariable. -/
theorem crossoverInternal_mem_retainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈
      orientedCrossings (PeriodicCNF.incidenceGraph formula))
    (internal : CrossoverInternal) :
    PeriodicPlanarSATVariable.crossoverInternal (crossing, internal) ∈
      (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  rw [retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_eq_map]
  apply List.mem_map.mpr
  refine ⟨Sum.inr (crossing, internal),
    crossoverInternal_mem_retainedDrawingPlanarSATFormula
      formula crossingMem internal, ?_⟩
  simp only [normalizePlanarSATVariable]
  rw [periodNormalize_eq_self_of_mem_orientedCrossings
    (PeriodicCNF.incidenceGraph formula) crossingMem]

end LeanTrominoes.PeriodicOrthocrossing

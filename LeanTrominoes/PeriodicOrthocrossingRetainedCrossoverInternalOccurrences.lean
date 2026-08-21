/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicOrthocrossingCrossoverInternalOccurrences

/-! # Retaining finite crossover-internal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every canonical crossing internal occurs in the complete retained finite
planar-SAT formula. -/
theorem crossoverInternal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈
      orientedCrossings (PeriodicCNF.incidenceGraph formula))
    (internal : CrossoverInternal) :
    (Sum.inr (crossing, internal) : PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_crossoverInternal_core_occurrence
    formula crossing internal
    (crossoverInternal_mem_drawingCarrierNodeCrossoverFormula
      (PeriodicCNF.incidenceGraph formula) crossingMem internal)

end LeanTrominoes.PeriodicOrthocrossing

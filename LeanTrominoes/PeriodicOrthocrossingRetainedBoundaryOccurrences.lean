/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicOrthocrossingCrossoverBoundaryOccurrences

/-! # Retained finite occurrences of canonical crossing boundaries -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every canonical crossing boundary occurs in the complete retained finite
planar-SAT formula. -/
theorem boundary_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries
      (PeriodicCNF.incidenceGraph formula)) :
    (Sum.inl (PlanarSATNode.carrier (.boundary boundary)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_boundary_crossover_occurrence
    formula boundary
    (drawingCrossingBoundary_mem_drawingCarrierNodeCrossoverFormula
      (PeriodicCNF.incidenceGraph formula) boundaryMem)

end LeanTrominoes.PeriodicOrthocrossing

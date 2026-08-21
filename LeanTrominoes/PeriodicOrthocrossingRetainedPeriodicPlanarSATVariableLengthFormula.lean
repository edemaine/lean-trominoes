/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicAtomVariableCount
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicVariableBlockLengths

/-! # Closed canonical retained variable-length formula -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- For a local incidence graph, the canonical retained variable enumeration
contains two terminals per segment, one atom per distinct source variable,
and thirteen boundary/internal names per oriented crossing. -/
theorem retainedDrawingPeriodicPlanarSATVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedDrawingPeriodicPlanarSATVariables formula).length =
      2 * (drawing formula.incidenceGraph).indexedSegments.length +
        formula.variableOccurrences.dedup.length +
          13 * (orientedCrossings formula.incidenceGraph).length := by
  unfold retainedDrawingPeriodicPlanarSATVariables
  simp only [List.length_append,
    retainedPeriodicTerminalVariables_length,
    retainedPeriodicBoundaryVariables_length,
    retainedPeriodicCrossoverInternalVariables_length]
  rw [retainedPeriodicAtomVariables_length formula isLocal]
  omega

end LeanTrominoes.PeriodicOrthocrossing

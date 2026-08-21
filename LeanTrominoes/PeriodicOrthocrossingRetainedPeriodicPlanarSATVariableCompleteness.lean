/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATTerminalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATBoundaryOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATAtomOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATCrossoverInternalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions

/-! # Completeness of retained periodic planar-SAT variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Under the occurrence-three bound, every geometrically valid canonical
protovariable occurs in the retained periodic planar-SAT formula. -/
theorem retainedDrawingPeriodicPlanarSATVariableValid_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {atom : PeriodicPlanarSATVariable Variable}
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    atom ∈ (retainedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences := by
  cases atom with
  | terminal indexed endpoint =>
      exact terminal_mem_retainedDrawingPeriodicPlanarSATFormula
        formula occurrences valid endpoint
  | boundary boundary =>
      exact boundary_mem_retainedDrawingPeriodicPlanarSATFormula
        formula valid
  | atom sourceAtom =>
      exact atom_mem_retainedDrawingPeriodicPlanarSATFormula
        formula valid
  | crossoverInternal taggedInternal =>
      rcases taggedInternal with ⟨crossing, internal⟩
      exact crossoverInternal_mem_retainedDrawingPeriodicPlanarSATFormula
        formula valid internal

end LeanTrominoes.PeriodicOrthocrossing

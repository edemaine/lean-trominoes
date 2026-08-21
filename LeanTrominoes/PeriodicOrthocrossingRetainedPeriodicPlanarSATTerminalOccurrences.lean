/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedZeroTerminalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATOccurrences

/-! # Periodic occurrences of canonical segment terminals -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Under the occurrence-three bound, both translation-zero terminals of
every indexed drawing segment survive periodicization as their canonical
terminal protovariables. -/
theorem terminal_mem_retainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈
      (drawing (PeriodicCNF.incidenceGraph formula)).indexedSegments)
    (endpoint : SegmentEnd) :
    PeriodicPlanarSATVariable.terminal indexed endpoint ∈
      (retainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  rw [retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_eq_map]
  apply List.mem_map.mpr
  refine
    ⟨Sum.inl
        (PlanarSATNode.carrier
          (.terminal ⟨indexed, (0, 0), endpoint⟩)),
      zeroTerminal_mem_retainedDrawingPlanarSATFormula
        formula occurrences indexedMem endpoint,
      rfl⟩

end LeanTrominoes.PeriodicOrthocrossing

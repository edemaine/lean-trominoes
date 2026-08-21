/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedTerminalOccurrences

/-! # Retained translation-zero terminal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Under the occurrence-three bound, both translation-zero terminals of
every indexed drawing segment occur in the retained finite formula. -/
theorem zeroTerminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈
      (drawing (PeriodicCNF.incidenceGraph formula)).indexedSegments)
    (endpoint : SegmentEnd) :
    (Sum.inl
        (PlanarSATNode.carrier
          (.terminal ⟨indexed, (0, 0), endpoint⟩)) :
      PlanarSATVariable Variable) ∈
        embeddedVariableOccurrences
          (retainedDrawingPlanarSATFormula formula) := by
  apply terminal_mem_retainedDrawingPlanarSATFormula formula occurrences
  apply List.mem_flatMap.mpr
  refine ⟨(indexed, (0, 0)), ?_, ?_⟩
  · apply (mem_neighborOccurrences_iff
      (PeriodicCNF.incidenceGraph formula) _).mpr
    exact ⟨indexedMem, by simp [IsNeighborTranslation]⟩
  · cases endpoint <;> simp [occurrenceTerminals]

end LeanTrominoes.PeriodicOrthocrossing

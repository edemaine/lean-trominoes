/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-! # Indexed segments of neighboring occurrence terminals -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A terminal enumerated from neighboring occurrences keeps a listed
indexed segment. -/
theorem retainedSegmentTerminal_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMember : terminal ∈ drawingSegmentTerminals graph) :
    terminal.indexed ∈ (drawing graph).indexedSegments := by
  rcases List.mem_flatMap.mp terminalMember with
    ⟨occurrence, occurrenceMember, terminalMember⟩
  have occurrenceData :=
    (mem_neighborOccurrences_iff graph occurrence).mp occurrenceMember
  simp only [occurrenceTerminals, List.mem_cons,
    List.not_mem_nil, or_false] at terminalMember
  rcases terminalMember with terminalEq | terminalEq <;>
    subst terminal <;> exact occurrenceData.1

end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership

/-! # Indexed segments of retained crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The first indexed segment of a retained crossing remains listed in the
drawing. -/
theorem retainedCrossing_first_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMember : record ∈ retainedCrossings graph) :
    record.first ∈ (drawing graph).indexedSegments := by
  rcases List.mem_flatMap.mp recordMember with
    ⟨canonical, canonicalMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨shift, _shiftMember, recordEq⟩
  rw [← recordEq]
  exact
    (orientedCrossingHalo_sound graph
      (orientedCrossings_subset_orientedCrossingHalo
        graph canonicalMember)).1

/-- The second indexed segment of a retained crossing remains listed in the
drawing. -/
theorem retainedCrossing_second_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMember : record ∈ retainedCrossings graph) :
    record.second ∈ (drawing graph).indexedSegments := by
  rcases List.mem_flatMap.mp recordMember with
    ⟨canonical, canonicalMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨shift, _shiftMember, recordEq⟩
  rw [← recordEq]
  exact
    (orientedCrossingHalo_sound graph
      (orientedCrossings_subset_orientedCrossingHalo
        graph canonicalMember)).2.1

end LeanTrominoes.PeriodicOrthocrossing

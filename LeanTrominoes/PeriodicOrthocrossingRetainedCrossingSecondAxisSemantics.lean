/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingSegmentTranslationSemantics

/-! # Second axis of retained crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The second segment of every retained oriented crossing is vertical. -/
theorem retainedCrossing_secondVertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMember : record ∈ retainedCrossings graph) :
    (record.secondSegment graph).IsVertical := by
  rcases List.mem_flatMap.mp recordMember with
    ⟨canonical, canonicalMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨shift, _shiftMember, recordEq⟩
  rw [← recordEq,
    CrossingRecord.secondSegment_retainedPeriodTranslate]
  exact
    (GridSegment.isVertical_translate _ _).mpr
      (orientedCrossingHalo_sound graph
        (orientedCrossings_subset_orientedCrossingHalo
          graph canonicalMember)).2.2.2.2.2.2.1

end LeanTrominoes.PeriodicOrthocrossing

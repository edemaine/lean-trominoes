/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossings

/-!
# Canonically oriented crossing sites

The raw crossing enumeration is symmetric in its two segment occurrences.
For gadget placement, we retain only the order in which the first occurrence
is horizontal.  Proper orthocrossing then forces the second occurrence to be
vertical.  Deduplication makes this an executable list with one record for
each resulting piece of finite crossing data.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Canonical gadget sites, ordered horizontal-first and deduplicated. -/
def orientedCrossings {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  ((canonicalCrossings graph).filter fun record =>
    (record.firstSegment graph).IsHorizontal).dedup

@[simp]
theorem mem_orientedCrossings_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    record ∈ orientedCrossings graph ↔
      record ∈ canonicalCrossings graph ∧
        (record.firstSegment graph).IsHorizontal := by
  simp [orientedCrossings]

theorem orientedCrossings_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (orientedCrossings graph).Nodup := by
  exact List.nodup_dedup _

/-- Every retained gadget site is a proper horizontal/vertical crossing of
two listed neighboring occurrences in the fundamental square. -/
theorem orientedCrossings_sound
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossings graph) :
    record.first ∈ (drawing graph).indexedSegments ∧
      record.second ∈ (drawing graph).indexedSegments ∧
      IsNeighborTranslation record.firstTranslate ∧
      IsNeighborTranslation record.secondTranslate ∧
      record.IsCanonical graph ∧
      (record.firstSegment graph).IsHorizontal ∧
      (record.secondSegment graph).IsVertical := by
  have oriented :=
    (mem_orientedCrossings_iff graph record).mp recordMem
  have sound := canonicalCrossings_sound graph oriented.1
  have canonical := sound.2.2.2.2
  have axes := canonical.2.2.2.2
  refine ⟨sound.1, sound.2.1, sound.2.2.1, sound.2.2.2.1,
    sound.2.2.2.2, oriented.2, ?_⟩
  rcases axes with horizontalVertical | verticalHorizontal
  · exact horizontalVertical.2
  · exact False.elim (verticalHorizontal.1.2 oriented.2.1)

/-- Every actual meeting of two distinct constructed occurrences in the
fundamental square appears in horizontal-first order. -/
theorem drawing_crossing_mem_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate)
    (pointFundamental : InFundamentalDrawingSquare graph point)
    (firstContains :
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          point)
    (secondContains :
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          point) :
    (⟨first, firstTranslate, second, secondTranslate, point⟩ :
        CrossingRecord) ∈ orientedCrossings graph ∨
      (⟨second, secondTranslate, first, firstTranslate, point⟩ :
        CrossingRecord) ∈ orientedCrossings graph := by
  have proper :=
    drawing_isOrthocrossing wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate point
      different firstContains secondContains
  rcases proper.2.2 with horizontalVertical | verticalHorizontal
  · left
    apply (mem_orientedCrossings_iff graph _).mpr
    exact ⟨drawing_crossing_mem_canonicalCrossings
      wellFormed degree isLocal firstMem secondMem different
        pointFundamental firstContains secondContains,
      horizontalVertical.1⟩
  · right
    apply (mem_orientedCrossings_iff graph _).mpr
    exact ⟨drawing_crossing_mem_canonicalCrossings
      wellFormed degree isLocal secondMem firstMem
        (fun equal => different equal.symm)
        pointFundamental secondContains firstContains,
      verticalHorizontal.2⟩

end PeriodicOrthocrossing
end LeanTrominoes

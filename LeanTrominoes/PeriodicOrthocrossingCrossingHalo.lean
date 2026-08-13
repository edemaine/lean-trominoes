/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonical

/-!
# Crossing halo for retained segment occurrences

The canonical crossing list contains one representative of every periodic
crossing in the fundamental drawing square.  The finite planar formula,
however, retains all nine neighboring translates of every segment so that
signal propagation can be proved for every occurrence needed at the boundary.
Two such retained occurrences can cross outside the fundamental square.

This file enumerates exactly those additional physical crossing sites.  For
each ordered pair of retained occurrences, the first horizontal and the second
vertical, there is only one possible intersection point: the vertical
carrier's column and the horizontal carrier's row.  Thus the halo needs no
larger point-grid search.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The only possible intersection point of a horizontal first segment and a
vertical second segment. -/
def orientedIntersectionPoint (first second : GridSegment) : Cell :=
  (second.start.1, first.start.2)

/-- Common interior containment by a horizontal and a vertical segment
identifies their uniquely determined intersection point. -/
theorem orientedIntersectionPoint_eq
    {first second : GridSegment} {point : Cell}
    (firstHorizontal : first.IsHorizontal)
    (secondVertical : second.IsVertical)
    (firstContains : first.InteriorContains point)
    (secondContains : second.InteriorContains point) :
    orientedIntersectionPoint first second = point := by
  have firstSame : point.2 = first.start.2 := by
    rcases firstContains with horizontal | vertical
    · exact horizontal.2.1
    · exact False.elim (firstHorizontal.2 vertical.1.1)
  have secondSame : point.1 = second.start.1 := by
    rcases secondContains with horizontal | vertical
    · exact False.elim (secondVertical.2 horizontal.1.1)
    · exact vertical.2.1
  exact Prod.ext secondSame.symm firstSame.symm

/-- One candidate record obtained from an ordered pair of retained segment
occurrences. -/
def orientedCrossingCandidate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : IndexedGridSegment × Cell) : CrossingRecord :=
  let firstSegment :=
    first.1.segment.translate
      ((drawing graph).periodTranslation first.2)
  let secondSegment :=
    second.1.segment.translate
      ((drawing graph).periodTranslation second.2)
  ⟨first.1, first.2, second.1, second.2,
    orientedIntersectionPoint firstSegment secondSegment⟩

/-- A genuine retained crossing, oriented horizontal first and vertical
second.  Unlike `CrossingRecord.IsCanonical`, the point may lie outside the
fundamental square. -/
def CrossingRecord.IsInCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) : Prop :=
  PeriodicGridDrawing.SegmentOccurrenceKey
      record.first record.firstTranslate ≠
    PeriodicGridDrawing.SegmentOccurrenceKey
      record.second record.secondTranslate ∧
  (record.firstSegment graph).IsHorizontal ∧
  (record.secondSegment graph).IsVertical ∧
  GridSegment.ProperlyCrossesAt
    (record.firstSegment graph)
    (record.secondSegment graph)
    record.point

instance {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    Decidable (record.IsInCrossingHalo graph) := by
  unfold CrossingRecord.IsInCrossingHalo
  infer_instance

/-- All ordered pairs of retained neighboring occurrences, equipped with
their only possible oriented intersection point. -/
def crossingHaloCandidates
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  (neighborOccurrences graph).flatMap fun first =>
    (neighborOccurrences graph).map fun second =>
      orientedCrossingCandidate graph first second

/-- Every proper crossing among the nine retained translates of every
constructed segment.  Deduplication makes the list an explicit finite set of
physical crossover sites. -/
def orientedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  ((crossingHaloCandidates graph).filter fun record =>
    record.IsInCrossingHalo graph).dedup

theorem orientedCrossingHalo_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (orientedCrossingHalo graph).Nodup := by
  exact List.nodup_dedup _

/-- Membership in the raw halo candidates is exactly membership of both
named neighboring occurrences together with the computed point. -/
theorem mem_crossingHaloCandidates_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    record ∈ crossingHaloCandidates graph ↔
      (record.first, record.firstTranslate) ∈ neighborOccurrences graph ∧
      (record.second, record.secondTranslate) ∈ neighborOccurrences graph ∧
      record.point =
        orientedIntersectionPoint
          (record.firstSegment graph)
          (record.secondSegment graph) := by
  constructor
  · intro recordMem
    rcases List.mem_flatMap.mp recordMem with
      ⟨first, firstMem, recordMem⟩
    rcases List.mem_map.mp recordMem with
      ⟨second, secondMem, recordEq⟩
    subst record
    exact ⟨firstMem, secondMem, rfl⟩
  · rcases record with
      ⟨first, firstTranslate, second, secondTranslate, point⟩
    rintro ⟨firstMem, secondMem, pointEq⟩
    apply List.mem_flatMap.mpr
    refine ⟨(first, firstTranslate), firstMem, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(second, secondTranslate), secondMem, ?_⟩
    simpa [orientedCrossingCandidate, CrossingRecord.firstSegment,
      CrossingRecord.secondSegment] using pointEq.symm

@[simp]
theorem mem_orientedCrossingHalo_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    record ∈ orientedCrossingHalo graph ↔
      (record.first, record.firstTranslate) ∈ neighborOccurrences graph ∧
      (record.second, record.secondTranslate) ∈ neighborOccurrences graph ∧
      record.point =
        orientedIntersectionPoint
          (record.firstSegment graph)
          (record.secondSegment graph) ∧
      record.IsInCrossingHalo graph := by
  rw [orientedCrossingHalo, List.mem_dedup, List.mem_filter]
  constructor
  · rintro ⟨candidate, halo⟩
    have data :=
      (mem_crossingHaloCandidates_iff graph record).mp candidate
    exact ⟨data.1, data.2.1, data.2.2, of_decide_eq_true halo⟩
  · rintro ⟨firstMem, secondMem, pointEq, halo⟩
    exact ⟨(mem_crossingHaloCandidates_iff graph record).mpr
        ⟨firstMem, secondMem, pointEq⟩,
      decide_eq_true halo⟩

/-- Every halo site is a proper horizontal/vertical crossing of two listed
neighboring segment occurrences. -/
theorem orientedCrossingHalo_sound
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossingHalo graph) :
    record.first ∈ (drawing graph).indexedSegments ∧
      record.second ∈ (drawing graph).indexedSegments ∧
      IsNeighborTranslation record.firstTranslate ∧
      IsNeighborTranslation record.secondTranslate ∧
      PeriodicGridDrawing.SegmentOccurrenceKey
          record.first record.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          record.second record.secondTranslate ∧
      (record.firstSegment graph).IsHorizontal ∧
      (record.secondSegment graph).IsVertical ∧
      GridSegment.ProperlyCrossesAt
        (record.firstSegment graph)
        (record.secondSegment graph)
        record.point := by
  have member := (mem_orientedCrossingHalo_iff graph record).mp recordMem
  have firstData :=
    (mem_neighborOccurrences_iff graph _).mp member.1
  have secondData :=
    (mem_neighborOccurrences_iff graph _).mp member.2.1
  exact ⟨firstData.1, secondData.1, firstData.2, secondData.2,
    member.2.2.2⟩

/-- Every canonical oriented crossing remains present in the larger physical
crossing halo. -/
theorem orientedCrossings_subset_orientedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossings graph) :
    record ∈ orientedCrossingHalo graph := by
  have sound := orientedCrossings_sound graph recordMem
  have canonical := sound.2.2.2.2.1
  apply (mem_orientedCrossingHalo_iff graph record).mpr
  refine ⟨(mem_neighborOccurrences_iff graph _).mpr
      ⟨sound.1, sound.2.2.1⟩,
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨sound.2.1, sound.2.2.2.1⟩, ?_, ?_⟩
  · exact (orientedIntersectionPoint_eq
      sound.2.2.2.2.2.1 sound.2.2.2.2.2.2
      canonical.2.2.1 canonical.2.2.2.1).symm
  · exact ⟨canonical.2.1, sound.2.2.2.2.2.1,
      sound.2.2.2.2.2.2, canonical.2.2⟩

/-- Every proper crossing between two retained neighboring occurrences
appears in horizontal-first order in the crossing halo. -/
theorem drawing_crossing_mem_orientedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (firstNeighbor : IsNeighborTranslation firstTranslate)
    (secondNeighbor : IsNeighborTranslation secondTranslate)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate)
    (firstContains :
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          point)
    (secondContains :
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          point) :
    (⟨first, firstTranslate, second, secondTranslate, point⟩ :
        CrossingRecord) ∈ orientedCrossingHalo graph ∨
      (⟨second, secondTranslate, first, firstTranslate, point⟩ :
        CrossingRecord) ∈ orientedCrossingHalo graph := by
  have proper :=
    drawing_isOrthocrossing wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate point
      different firstContains secondContains
  rcases proper.2.2 with horizontalVertical | verticalHorizontal
  · left
    apply (mem_orientedCrossingHalo_iff graph _).mpr
    refine ⟨(mem_neighborOccurrences_iff graph _).mpr
        ⟨firstMem, firstNeighbor⟩,
      (mem_neighborOccurrences_iff graph _).mpr
        ⟨secondMem, secondNeighbor⟩, ?_, ?_⟩
    · exact (orientedIntersectionPoint_eq
        horizontalVertical.1 horizontalVertical.2
        firstContains secondContains).symm
    · exact ⟨different, horizontalVertical.1,
        horizontalVertical.2, proper⟩
  · right
    apply (mem_orientedCrossingHalo_iff graph _).mpr
    refine ⟨(mem_neighborOccurrences_iff graph _).mpr
        ⟨secondMem, secondNeighbor⟩,
      (mem_neighborOccurrences_iff graph _).mpr
        ⟨firstMem, firstNeighbor⟩, ?_, ?_⟩
    · exact (orientedIntersectionPoint_eq
        verticalHorizontal.2 verticalHorizontal.1
        secondContains firstContains).symm
    · exact ⟨fun equal => different equal.symm,
        verticalHorizontal.2, verticalHorizontal.1,
        GridSegment.properlyCrossesAt_symm proper⟩

end PeriodicOrthocrossing
end LeanTrominoes

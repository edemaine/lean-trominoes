/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBounds
import LeanTrominoes.PeriodicOrthocrossingNeighborTranslationsData

/-!
# Finite enumeration of canonical crossings

The endpoint bounds reduce all occurrences meeting the fundamental square to
the nine neighboring cell translations.  We pair those finite occurrences
with every integer point in the square and retain exactly the proper crossings
between distinct occurrence keys.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

@[simp]
theorem mem_neighborCoordinates_iff (coordinate : Int) :
    coordinate ∈ neighborCoordinates ↔
      coordinate = -1 ∨ coordinate = 0 ∨ coordinate = 1 := by
  simp [neighborCoordinates]

@[simp]
theorem mem_neighborTranslations_iff (translate : Cell) :
    translate ∈ neighborTranslations ↔
      IsNeighborTranslation translate := by
  rcases translate with ⟨horizontal, vertical⟩
  constructor
  · intro translateMem
    rcases List.mem_flatMap.mp translateMem with
      ⟨horizontal', horizontalMem, translateMem⟩
    rcases List.mem_map.mp translateMem with
      ⟨vertical', verticalMem, translateEq⟩
    cases translateEq
    exact ⟨(mem_neighborCoordinates_iff horizontal).mp horizontalMem,
      (mem_neighborCoordinates_iff vertical).mp verticalMem⟩
  · rintro ⟨horizontalNeighbor, verticalNeighbor⟩
    apply List.mem_flatMap.mpr
    refine ⟨horizontal,
      (mem_neighborCoordinates_iff horizontal).mpr horizontalNeighbor, ?_⟩
    exact List.mem_map.mpr
      ⟨vertical,
        (mem_neighborCoordinates_iff vertical).mpr verticalNeighbor, rfl⟩

theorem neighborCoordinates_nodup : neighborCoordinates.Nodup := by
  decide

theorem neighborTranslations_nodup : neighborTranslations.Nodup := by
  native_decide

/-- Every indexed segment paired with each neighboring cell translation. -/
def neighborOccurrences {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (IndexedGridSegment × Cell) :=
  (drawing graph).indexedSegments.flatMap fun indexed =>
    neighborTranslations.map fun translate =>
      (indexed, translate)

@[simp]
theorem mem_neighborOccurrences_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (occurrence : IndexedGridSegment × Cell) :
    occurrence ∈ neighborOccurrences graph ↔
      occurrence.1 ∈ (drawing graph).indexedSegments ∧
        IsNeighborTranslation occurrence.2 := by
  rcases occurrence with ⟨indexed, translate⟩
  simp [neighborOccurrences, Prod.ext_iff]

/-- Integer coordinates of one half-open drawing period. -/
def fundamentalCoordinates {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : List Int :=
  (List.range (drawingGridSize graph)).map Int.ofNat

@[simp]
theorem mem_fundamentalCoordinates_iff
    {Vertex : Type*} (graph : PeriodicGraph Vertex) (coordinate : Int) :
    coordinate ∈ fundamentalCoordinates graph ↔
      0 ≤ coordinate ∧ coordinate < drawingGridSize graph := by
  constructor
  · intro coordinateMem
    rcases List.mem_map.mp coordinateMem with
      ⟨natural, naturalMem, coordinateEq⟩
    subst coordinate
    have naturalLt := List.mem_range.mp naturalMem
    constructor
    · exact Int.natCast_nonneg natural
    · exact Int.ofNat_lt.mpr naturalLt
  · rintro ⟨coordinateNonnegative, coordinateLt⟩
    apply List.mem_map.mpr
    refine ⟨coordinate.toNat, List.mem_range.mpr ?_, ?_⟩
    · rw [Int.toNat_lt coordinateNonnegative]
      exact coordinateLt
    · simpa using Int.toNat_of_nonneg coordinateNonnegative

/-- Integer points of the canonical half-open fundamental square. -/
def fundamentalPoints {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : List Cell :=
  (fundamentalCoordinates graph).flatMap fun horizontal =>
    (fundamentalCoordinates graph).map fun vertical =>
      (horizontal, vertical)

@[simp]
theorem mem_fundamentalPoints_iff
    {Vertex : Type*} (graph : PeriodicGraph Vertex) (point : Cell) :
    point ∈ fundamentalPoints graph ↔
      InFundamentalDrawingSquare graph point := by
  rcases point with ⟨horizontal, vertical⟩
  constructor
  · intro pointMem
    rcases List.mem_flatMap.mp pointMem with
      ⟨horizontal', horizontalMem, pointMem⟩
    rcases List.mem_map.mp pointMem with
      ⟨vertical', verticalMem, pointEq⟩
    cases pointEq
    have horizontalBounds :=
      (mem_fundamentalCoordinates_iff graph horizontal).mp horizontalMem
    have verticalBounds :=
      (mem_fundamentalCoordinates_iff graph vertical).mp verticalMem
    exact ⟨horizontalBounds.1, horizontalBounds.2,
      verticalBounds.1, verticalBounds.2⟩
  · rintro ⟨horizontalNonnegative, horizontalLt,
      verticalNonnegative, verticalLt⟩
    apply List.mem_flatMap.mpr
    refine ⟨horizontal,
      (mem_fundamentalCoordinates_iff graph horizontal).mpr
        ⟨horizontalNonnegative, horizontalLt⟩, ?_⟩
    exact List.mem_map.mpr
      ⟨vertical,
        (mem_fundamentalCoordinates_iff graph vertical).mpr
          ⟨verticalNonnegative, verticalLt⟩, rfl⟩

/-- Finite data naming one candidate crossing occurrence in the canonical
fundamental square. -/
structure CrossingRecord where
  first : IndexedGridSegment
  firstTranslate : Cell
  second : IndexedGridSegment
  secondTranslate : Cell
  point : Cell
  deriving DecidableEq, Repr

/-- The two translated geometric segments named by a crossing record. -/
def CrossingRecord.firstSegment {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) : GridSegment :=
  record.first.segment.translate
    ((drawing graph).periodTranslation record.firstTranslate)

def CrossingRecord.secondSegment {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) : GridSegment :=
  record.second.segment.translate
    ((drawing graph).periodTranslation record.secondTranslate)

/-- A genuine canonical crossing: distinct occurrence keys meeting properly
at a point in the fundamental square. -/
def CrossingRecord.IsCanonical {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) : Prop :=
  InFundamentalDrawingSquare graph record.point ∧
    PeriodicGridDrawing.SegmentOccurrenceKey
        record.first record.firstTranslate ≠
      PeriodicGridDrawing.SegmentOccurrenceKey
        record.second record.secondTranslate ∧
    GridSegment.ProperlyCrossesAt
      (record.firstSegment graph)
      (record.secondSegment graph)
      record.point

instance {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) :
    Decidable (record.IsCanonical graph) := by
  unfold CrossingRecord.IsCanonical InFundamentalDrawingSquare
  infer_instance

/-- All finite neighbor-occurrence/point combinations before filtering. -/
def crossingCandidates {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  (neighborOccurrences graph).flatMap fun first =>
    (neighborOccurrences graph).flatMap fun second =>
      (fundamentalPoints graph).map fun point =>
        ⟨first.1, first.2, second.1, second.2, point⟩

/-- The executable list of proper crossings in one fundamental square. -/
def canonicalCrossings {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  (crossingCandidates graph).filter fun record =>
    record.IsCanonical graph

theorem mem_crossingCandidates
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : IndexedGridSegment}
    {firstTranslate secondTranslate point : Cell}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    (firstNeighbor : IsNeighborTranslation firstTranslate)
    (secondNeighbor : IsNeighborTranslation secondTranslate)
    (pointFundamental : InFundamentalDrawingSquare graph point) :
    (⟨first, firstTranslate, second, secondTranslate, point⟩ :
        CrossingRecord) ∈ crossingCandidates graph := by
  apply List.mem_flatMap.mpr
  refine ⟨(first, firstTranslate),
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨firstMem, firstNeighbor⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(second, secondTranslate),
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨secondMem, secondNeighbor⟩, ?_⟩
  exact List.mem_map.mpr
    ⟨point, (mem_fundamentalPoints_iff graph point).mpr pointFundamental,
      rfl⟩

/-- Every enumerated record is a proper crossing of two listed neighboring
occurrences in the canonical fundamental square. -/
theorem canonicalCrossings_sound
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ canonicalCrossings graph) :
    record.first ∈ (drawing graph).indexedSegments ∧
      record.second ∈ (drawing graph).indexedSegments ∧
      IsNeighborTranslation record.firstTranslate ∧
      IsNeighborTranslation record.secondTranslate ∧
      record.IsCanonical graph := by
  rw [canonicalCrossings, List.mem_filter] at recordMem
  rcases recordMem with ⟨candidateMem, canonical⟩
  have canonical' : record.IsCanonical graph :=
    of_decide_eq_true canonical
  simp only [crossingCandidates, List.mem_flatMap] at candidateMem
  rcases candidateMem with
    ⟨first, firstMem, candidateMem⟩
  rcases candidateMem with
    ⟨second, secondMem, candidateMem⟩
  simp only [List.mem_map] at candidateMem
  rcases candidateMem with ⟨point, pointMem, recordEq⟩
  subst record
  have firstData :=
    (mem_neighborOccurrences_iff graph first).mp firstMem
  have secondData :=
    (mem_neighborOccurrences_iff graph second).mp secondMem
  exact ⟨firstData.1, secondData.1,
    firstData.2, secondData.2, canonical'⟩

/-- Every actual meeting of distinct constructed occurrences in the
fundamental square appears in the executable canonical crossing list. -/
theorem drawing_crossing_mem_canonicalCrossings
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
        CrossingRecord) ∈ canonicalCrossings graph := by
  have firstNeighbor :=
    drawing_occurrence_translate_isNeighbor
      wellFormed degree isLocal firstMem
        pointFundamental firstContains
  have secondNeighbor :=
    drawing_occurrence_translate_isNeighbor
      wellFormed degree isLocal secondMem
        pointFundamental secondContains
  have proper :=
    drawing_isOrthocrossing wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate point
      different firstContains secondContains
  apply List.mem_filter.mpr
  exact ⟨mem_crossingCandidates graph
      firstMem secondMem firstNeighbor secondNeighbor pointFundamental,
    decide_eq_true
      ⟨pointFundamental, different, proper⟩⟩

end PeriodicOrthocrossing
end LeanTrominoes

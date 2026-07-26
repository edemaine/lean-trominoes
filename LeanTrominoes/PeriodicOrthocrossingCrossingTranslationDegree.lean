import LeanTrominoes.PeriodicOrthocrossingTranslationDegree
import LeanTrominoes.PeriodicOrthocrossingPlanarWires

/-!
# Degree of crossing-bearing segment translates

For one indexed segment, this file extracts the neighboring translations
that actually participate in canonical crossings.  Every such translation
meets the fundamental square, so the geometric two-translate bound applies.
Crossing boundaries are then projected to their indexed segment and
translation and shown to lie in this bounded set.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

noncomputable def segmentCrossingTranslations
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) : Finset Cell := by
  classical
  exact neighborTranslations.toFinset.filter fun translate =>
    ∃ record ∈ orientedCrossings graph,
      (record.first = indexed ∧ record.firstTranslate = translate) ∨
        (record.second = indexed ∧ record.secondTranslate = translate)

theorem mem_segmentCrossingTranslations_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (translate : Cell) :
    translate ∈ segmentCrossingTranslations graph indexed ↔
      IsNeighborTranslation translate ∧
        ∃ record ∈ orientedCrossings graph,
          (record.first = indexed ∧ record.firstTranslate = translate) ∨
            (record.second = indexed ∧
              record.secondTranslate = translate) := by
  classical
  simp [segmentCrossingTranslations]

theorem segmentCrossingTranslations_subset_fundamentalMeetingTranslations
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) :
    segmentCrossingTranslations graph indexed ⊆
      fundamentalMeetingTranslations graph indexed := by
  classical
  intro translate translateMem
  have translateData :=
    (mem_segmentCrossingTranslations_iff
      graph indexed translate).mp translateMem
  apply (mem_fundamentalMeetingTranslations_iff
    graph indexed translate).mpr
  refine ⟨translateData.1, ?_⟩
  rcases translateData.2 with
    ⟨record, recordMem, first | second⟩
  · rcases first with ⟨indexedEq, translateEq⟩
    have sound := orientedCrossings_sound graph recordMem
    have canonical := sound.2.2.2.2.1
    refine ⟨record.point, canonical.1, ?_⟩
    simpa [CrossingRecord.firstSegment,
      indexedEq, translateEq] using canonical.2.2.1
  · rcases second with ⟨indexedEq, translateEq⟩
    have sound := orientedCrossings_sound graph recordMem
    have canonical := sound.2.2.2.2.1
    refine ⟨record.point, canonical.1, ?_⟩
    simpa [CrossingRecord.secondSegment,
      indexedEq, translateEq] using canonical.2.2.2.1

theorem segmentCrossingTranslations_card_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments) :
    (segmentCrossingTranslations graph indexed).card ≤ 2 := by
  exact (Finset.card_le_card
      (segmentCrossingTranslations_subset_fundamentalMeetingTranslations
        graph indexed)).trans
    (fundamentalMeetingTranslations_card_le_two
      wellFormed degree isLocal indexedMem)

def CrossingBoundary.indexed (boundary : CrossingBoundary) :
    IndexedGridSegment :=
  match boundary.side with
  | .left | .right => boundary.crossing.first
  | .top | .bottom => boundary.crossing.second

def CrossingBoundary.translate (boundary : CrossingBoundary) : Cell :=
  match boundary.side with
  | .left | .right => boundary.crossing.firstTranslate
  | .top | .bottom => boundary.crossing.secondTranslate

@[simp]
theorem CrossingBoundary.carrierKey_eq_indexed_translate
    (boundary : CrossingBoundary) :
    boundary.carrierKey =
      PeriodicGridDrawing.SegmentOccurrenceKey
        boundary.indexed boundary.translate := by
  cases boundary
  case mk crossing side =>
    cases side <;> rfl

theorem drawingCrossingBoundary_indexed_mem_and_translate_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph) :
    boundary.indexed ∈ (drawing graph).indexedSegments ∧
      boundary.translate ∈
        segmentCrossingTranslations graph boundary.indexed := by
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨record, recordMem, boundaryMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at boundaryMem
  have sound := orientedCrossings_sound graph recordMem
  rcases boundaryMem with
    boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
      subst boundary
  · refine ⟨sound.1, ?_⟩
    apply (mem_segmentCrossingTranslations_iff
      graph record.first record.firstTranslate).mpr
    exact ⟨sound.2.2.1, record, recordMem, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨sound.1, ?_⟩
    apply (mem_segmentCrossingTranslations_iff
      graph record.first record.firstTranslate).mpr
    exact ⟨sound.2.2.1, record, recordMem, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨sound.2.1, ?_⟩
    apply (mem_segmentCrossingTranslations_iff
      graph record.second record.secondTranslate).mpr
    exact ⟨sound.2.2.2.1, record, recordMem, Or.inr ⟨rfl, rfl⟩⟩
  · refine ⟨sound.2.1, ?_⟩
    apply (mem_segmentCrossingTranslations_iff
      graph record.second record.secondTranslate).mpr
    exact ⟨sound.2.2.2.1, record, recordMem, Or.inr ⟨rfl, rfl⟩⟩

end PeriodicOrthocrossing
end LeanTrominoes

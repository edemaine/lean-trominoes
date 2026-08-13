/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRetentionBounds
import LeanTrominoes.PeriodicOrthocrossingCarrierLensGeometry

/-!
# Geometry of retained crossing boundaries

Every retained crossing is a common period translate of a canonical proper
crossing.  Thus its two indexed segments remain listed, and each boundary's
crossing point lies in the interior of the exact segment occurrence named by
its carrier key.  These facts are themselves covariant under further common
period translation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Translating a crossing record translates its first physical segment
occurrence by the same drawing-period vector. -/
theorem CrossingRecord.firstSegment_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).firstSegment graph =
      (record.firstSegment graph).translate
        ((drawing graph).periodTranslation shift) := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases first.segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases firstTranslate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.firstSegment,
    GridSegment.translate,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]
  constructor <;> constructor <;> ring

/-- The analogous covariance statement for the second occurrence. -/
theorem CrossingRecord.secondSegment_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    (record.periodTranslate graph shift).secondSegment graph =
      (record.secondSegment graph).translate
        ((drawing graph).periodTranslation shift) := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases second.segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases secondTranslate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.secondSegment,
    GridSegment.translate,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]
  constructor <;> constructor <;> ring

/-- Every retained crossing remains a proper horizontal/vertical crossing of
two listed indexed drawing segments. -/
theorem retainedCrossings_sound
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ retainedCrossings graph) :
    record.first ∈ (drawing graph).indexedSegments ∧
      record.second ∈ (drawing graph).indexedSegments ∧
      GridSegment.ProperlyCrossesAt
        (record.firstSegment graph)
        (record.secondSegment graph)
        record.point := by
  rcases List.mem_flatMap.mp recordMem with
    ⟨canonical, canonicalMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨shift, _shiftMem, recordEq⟩
  rw [← recordEq]
  have sound :=
    orientedCrossingHalo_sound graph
      (orientedCrossings_subset_orientedCrossingHalo
        graph canonicalMem)
  have proper := sound.2.2.2.2.2.2.2
  let offset := (drawing graph).periodTranslation shift
  have firstContains :
      GridSegment.InteriorContains
        ((canonical.periodTranslate graph shift).firstSegment graph)
        (canonical.periodTranslate graph shift).point := by
    rw [CrossingRecord.firstSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (canonical.firstSegment graph) offset canonical.point).mpr
          proper.1
  have secondContains :
      GridSegment.InteriorContains
        ((canonical.periodTranslate graph shift).secondSegment graph)
        (canonical.periodTranslate graph shift).point := by
    rw [CrossingRecord.secondSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (canonical.secondSegment graph) offset canonical.point).mpr
          proper.2.1
  have firstHorizontal :
      GridSegment.IsHorizontal
        ((canonical.periodTranslate graph shift).firstSegment graph) := by
    rw [CrossingRecord.firstSegment_periodTranslate]
    exact
      (GridSegment.isHorizontal_translate _ _).mpr
        sound.2.2.2.2.2.1
  have secondVertical :
      GridSegment.IsVertical
        ((canonical.periodTranslate graph shift).secondSegment graph) := by
    rw [CrossingRecord.secondSegment_periodTranslate]
    exact
      (GridSegment.isVertical_translate _ _).mpr
        sound.2.2.2.2.2.2.1
  exact ⟨sound.1, sound.2.1,
    firstContains, secondContains,
    Or.inl ⟨firstHorizontal, secondVertical⟩⟩

/-- A retained boundary names a listed segment, and its crossing point lies
in the interior of the exact occurrence selected by its side. -/
theorem retainedCrossingBoundary_indexed_mem_and_contains
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph) :
    boundary.indexed ∈ (drawing graph).indexedSegments ∧
      GridSegment.InteriorContains
        (boundary.indexed.segment.translate
          ((drawing graph).periodTranslation boundary.translate))
        boundary.crossing.point := by
  have recordMem :=
    retainedCrossingBoundary_crossing_mem graph boundaryMem
  have sound := retainedCrossings_sound graph recordMem
  rcases boundary with ⟨record, side⟩
  cases side
  · exact ⟨sound.1, sound.2.2.1⟩
  · exact ⟨sound.1, sound.2.2.1⟩
  · exact ⟨sound.2.1, sound.2.2.2.1⟩
  · exact ⟨sound.2.1, sound.2.2.2.1⟩

/-- Further period translation does not change the indexed segment named by
a crossing boundary. -/
@[simp]
theorem CrossingBoundary.indexed_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    (boundary.periodTranslate graph shift).indexed =
      boundary.indexed := by
  rcases boundary with ⟨record, side⟩
  cases side <;> rfl

/-- Further period translation adds the common shift to the boundary's
occurrence translation. -/
@[simp]
theorem CrossingBoundary.translate_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    (boundary.periodTranslate graph shift).translate =
      Cell.add boundary.translate shift := by
  rcases boundary with ⟨record, side⟩
  cases side <;> rfl

/-- The physical supporting occurrence of a translated boundary is the
common translate of its original supporting occurrence. -/
theorem CrossingBoundary.supportingSegment_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    (boundary.periodTranslate graph shift).indexed.segment.translate
        ((drawing graph).periodTranslation
          (boundary.periodTranslate graph shift).translate) =
      (boundary.indexed.segment.translate
        ((drawing graph).periodTranslation boundary.translate)).translate
          ((drawing graph).periodTranslation shift) := by
  rcases boundary with ⟨record, side⟩
  cases side
  · exact CrossingRecord.firstSegment_periodTranslate graph record shift
  · exact CrossingRecord.firstSegment_periodTranslate graph record shift
  · exact CrossingRecord.secondSegment_periodTranslate graph record shift
  · exact CrossingRecord.secondSegment_periodTranslate graph record shift

/-- Interior containment by a boundary's supporting occurrence is invariant
under common period translation. -/
theorem CrossingBoundary.supportingSegment_contains_periodTranslate_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) (shift : Cell) :
    GridSegment.InteriorContains
        ((boundary.periodTranslate graph shift).indexed.segment.translate
          ((drawing graph).periodTranslation
            (boundary.periodTranslate graph shift).translate))
        (boundary.periodTranslate graph shift).crossing.point ↔
      GridSegment.InteriorContains
        (boundary.indexed.segment.translate
          ((drawing graph).periodTranslation boundary.translate))
        boundary.crossing.point := by
  rw [CrossingBoundary.supportingSegment_periodTranslate]
  change
    ((boundary.indexed.segment.translate
      ((drawing graph).periodTranslation boundary.translate)).translate
        ((drawing graph).periodTranslation shift)).InteriorContains
      (Cell.add boundary.crossing.point
        ((drawing graph).periodTranslation shift)) ↔ _
  exact
    PeriodicGridDrawing.interiorContains_translate_iff
      (boundary.indexed.segment.translate
        ((drawing graph).periodTranslation boundary.translate))
      ((drawing graph).periodTranslation shift)
      boundary.crossing.point

/-- Translating a retained boundary preserves listed indexed-segment
membership and supporting-occurrence containment, even if the translated
boundary lies outside the chosen finite orbit window. -/
theorem retainedCrossingBoundary_periodTranslate_indexed_mem_and_contains
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph)
    (shift : Cell) :
    (boundary.periodTranslate graph shift).indexed ∈
        (drawing graph).indexedSegments ∧
      GridSegment.InteriorContains
        ((boundary.periodTranslate graph shift).indexed.segment.translate
          ((drawing graph).periodTranslation
            (boundary.periodTranslate graph shift).translate))
        (boundary.periodTranslate graph shift).crossing.point := by
  have data :=
    retainedCrossingBoundary_indexed_mem_and_contains
      graph boundaryMem
  exact ⟨by simpa using data.1,
    (CrossingBoundary.supportingSegment_contains_periodTranslate_iff
      graph boundary shift).mpr data.2⟩

end PeriodicOrthocrossing
end LeanTrominoes

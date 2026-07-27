import LeanTrominoes.PeriodicOrthocrossingCrossingHalo
import LeanTrominoes.PeriodicGridDrawingFinitePlanarity

/-!
# Periodic normalization of crossing-halo records

Crossing-halo sites are physical translates of canonical crossing sites.
This file computes the common lattice translation from the crossing point,
subtracts it from both segment-occurrence translations, and reduces the
point into the half-open fundamental square.  A genuine halo record thereby
normalizes to an executable member of `orientedCrossings`.

Keeping the common shift explicit is important when the finite planar formula
is periodicized: translated crossover variables can use the canonical record
as proto-variable and carry the shift as their literal offset.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The drawing-cell quotient containing a crossing point. -/
def crossingPeriodShift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) : Cell :=
  (record.point.1 / drawingGridSize graph,
    record.point.2 / drawingGridSize graph)

/-- Subtract the crossing point's common period shift from both occurrence
translations and from the physical crossing point. -/
def CrossingRecord.periodNormalize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    CrossingRecord :=
  let shift := crossingPeriodShift graph record
  ⟨record.first, Cell.sub record.firstTranslate shift,
    record.second, Cell.sub record.secondTranslate shift,
    PeriodicGridDrawing.normalizePoint
      (drawing graph) record.point shift⟩

/-- The normalized crossing point lies in the canonical half-open drawing
square. -/
theorem periodNormalize_point_inFundamental
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    InFundamentalDrawingSquare graph
      (record.periodNormalize graph).point := by
  have sizePositiveNat : 0 < drawingGridSize graph :=
    drawingGridSize_pos graph
  have sizePositive :
      (0 : Int) < drawingGridSize graph := by
    exact_mod_cast sizePositiveNat
  have sizeNe : (drawingGridSize graph : Int) ≠ 0 :=
    ne_of_gt sizePositive
  have firstNonnegative :=
    Int.emod_nonneg record.point.1 sizeNe
  have firstLt :=
    Int.emod_lt_of_pos record.point.1 sizePositive
  have secondNonnegative :=
    Int.emod_nonneg record.point.2 sizeNe
  have secondLt :=
    Int.emod_lt_of_pos record.point.2 sizePositive
  have firstEq :
      record.point.1 -
          (drawingGridSize graph : Int) *
            (record.point.1 / drawingGridSize graph) =
        record.point.1 % drawingGridSize graph := by
    have division :=
      Int.emod_add_mul_ediv record.point.1
        (drawingGridSize graph : Int)
    omega
  have secondEq :
      record.point.2 -
          (drawingGridSize graph : Int) *
            (record.point.2 / drawingGridSize graph) =
        record.point.2 % drawingGridSize graph := by
    have division :=
      Int.emod_add_mul_ediv record.point.2
        (drawingGridSize graph : Int)
    omega
  simpa [CrossingRecord.periodNormalize,
    PeriodicGridDrawing.normalizePoint,
    crossingPeriodShift,
    PeriodicGridDrawing.periodTranslation,
    drawing_gridSize, InFundamentalDrawingSquare,
    Cell.sub, Cell.scale, firstEq, secondEq] using
      And.intro firstNonnegative
        (And.intro firstLt
          (And.intro secondNonnegative secondLt))

/-- Adding the extracted period translation recovers the physical crossing
point. -/
theorem periodNormalize_point_add_shift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    Cell.add (record.periodNormalize graph).point
        ((drawing graph).periodTranslation
          (crossingPeriodShift graph record)) =
      record.point := by
  exact PeriodicGridDrawing.normalizePoint_add
    (drawing graph) record.point (crossingPeriodShift graph record)

/-- Adding the extracted common shift back to the normalized first
occurrence translation recovers the physical occurrence translation. -/
theorem periodNormalize_firstTranslate_add_shift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    Cell.add (record.periodNormalize graph).firstTranslate
        (crossingPeriodShift graph record) =
      record.firstTranslate := by
  rcases shiftEq : crossingPeriodShift graph record with
    ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [CrossingRecord.periodNormalize, shiftEq,
      Cell.add, Cell.sub]

/-- The analogous reconstruction identity for the second occurrence
translation. -/
theorem periodNormalize_secondTranslate_add_shift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    Cell.add (record.periodNormalize graph).secondTranslate
        (crossingPeriodShift graph record) =
      record.secondTranslate := by
  rcases shiftEq : crossingPeriodShift graph record with
    ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [CrossingRecord.periodNormalize, shiftEq,
      Cell.add, Cell.sub]

/-- The normalized first occurrence, translated back by the extracted common
shift, is the original physical first occurrence. -/
theorem periodNormalize_firstSegment_translate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    ((record.periodNormalize graph).firstSegment graph).translate
        ((drawing graph).periodTranslation
          (crossingPeriodShift graph record)) =
      record.firstSegment graph := by
  simpa [CrossingRecord.periodNormalize,
    CrossingRecord.firstSegment] using
    PeriodicGridDrawing.translate_relative
      (drawing graph) record.first.segment
      record.firstTranslate (crossingPeriodShift graph record)

/-- The same translation identity for the second occurrence. -/
theorem periodNormalize_secondSegment_translate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    ((record.periodNormalize graph).secondSegment graph).translate
        ((drawing graph).periodTranslation
          (crossingPeriodShift graph record)) =
      record.secondSegment graph := by
  simpa [CrossingRecord.periodNormalize,
    CrossingRecord.secondSegment] using
    PeriodicGridDrawing.translate_relative
      (drawing graph) record.second.segment
      record.secondTranslate (crossingPeriodShift graph record)

/-- Subtracting one common shift from occurrence translations preserves
inequality of occurrence keys. -/
theorem periodNormalize_occurrenceKeys_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          record.first record.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          record.second record.secondTranslate) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        (record.periodNormalize graph).first
        (record.periodNormalize graph).firstTranslate ≠
      PeriodicGridDrawing.SegmentOccurrenceKey
        (record.periodNormalize graph).second
        (record.periodNormalize graph).secondTranslate := by
  intro normalizedEqual
  apply different
  rcases crossingEq : crossingPeriodShift graph record with
    ⟨shiftX, shiftY⟩
  simp only [CrossingRecord.periodNormalize,
    crossingEq, PeriodicGridDrawing.SegmentOccurrenceKey,
    Cell.sub, Prod.mk.injEq] at normalizedEqual ⊢
  rcases normalizedEqual with
    ⟨routeEq, segmentEq, translateXEq, translateYEq⟩
  exact ⟨routeEq, segmentEq, Prod.ext (by omega) (by omega)⟩

/-- Proper crossing is preserved when both occurrences and the crossing
point are normalized by their common period translation. -/
theorem periodNormalize_properlyCrossesAt
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord)
    (proper :
      GridSegment.ProperlyCrossesAt
        (record.firstSegment graph)
        (record.secondSegment graph)
        record.point) :
    GridSegment.ProperlyCrossesAt
      ((record.periodNormalize graph).firstSegment graph)
      ((record.periodNormalize graph).secondSegment graph)
      (record.periodNormalize graph).point := by
  let shift :=
    (drawing graph).periodTranslation
      (crossingPeriodShift graph record)
  have pointEq :
      Cell.add (record.periodNormalize graph).point shift =
        record.point :=
    periodNormalize_point_add_shift graph record
  have firstEq :
      ((record.periodNormalize graph).firstSegment graph).translate shift =
        record.firstSegment graph :=
    periodNormalize_firstSegment_translate graph record
  have secondEq :
      ((record.periodNormalize graph).secondSegment graph).translate shift =
        record.secondSegment graph :=
    periodNormalize_secondSegment_translate graph record
  have firstContains :
      ((record.periodNormalize graph).firstSegment graph).InteriorContains
        (record.periodNormalize graph).point := by
    apply (PeriodicGridDrawing.interiorContains_translate_iff
      ((record.periodNormalize graph).firstSegment graph)
      shift (record.periodNormalize graph).point).mp
    simpa [firstEq, pointEq] using proper.1
  have secondContains :
      ((record.periodNormalize graph).secondSegment graph).InteriorContains
        (record.periodNormalize graph).point := by
    apply (PeriodicGridDrawing.interiorContains_translate_iff
      ((record.periodNormalize graph).secondSegment graph)
      shift (record.periodNormalize graph).point).mp
    simpa [secondEq, pointEq] using proper.2.1
  have axes :
      (((record.periodNormalize graph).firstSegment graph).IsHorizontal ∧
          ((record.periodNormalize graph).secondSegment graph).IsVertical) ∨
        (((record.periodNormalize graph).firstSegment graph).IsVertical ∧
          ((record.periodNormalize graph).secondSegment graph).IsHorizontal) := by
    rcases proper.2.2 with horizontalVertical | verticalHorizontal
    · left
      exact ⟨(GridSegment.isHorizontal_translate _ shift).mp
          (firstEq ▸ horizontalVertical.1),
        (GridSegment.isVertical_translate _ shift).mp
          (secondEq ▸ horizontalVertical.2)⟩
    · right
      exact ⟨(GridSegment.isVertical_translate _ shift).mp
          (firstEq ▸ verticalHorizontal.1),
        (GridSegment.isHorizontal_translate _ shift).mp
          (secondEq ▸ verticalHorizontal.2)⟩
  exact ⟨firstContains, secondContains, axes⟩

/-- Every genuine halo crossing normalizes to the canonical oriented crossing
list used as the periodic quotient. -/
theorem periodNormalize_mem_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossingHalo graph) :
    record.periodNormalize graph ∈ orientedCrossings graph := by
  have sound := orientedCrossingHalo_sound graph recordMem
  have proper :=
    periodNormalize_properlyCrossesAt graph record sound.2.2.2.2.2.2.2
  have different :=
    periodNormalize_occurrenceKeys_ne graph record
      sound.2.2.2.2.1
  have firstHorizontal :
      ((record.periodNormalize graph).firstSegment graph).IsHorizontal := by
    let shift :=
      (drawing graph).periodTranslation
        (crossingPeriodShift graph record)
    apply (GridSegment.isHorizontal_translate _ shift).mp
    rw [periodNormalize_firstSegment_translate graph record]
    exact sound.2.2.2.2.2.1
  apply (mem_orientedCrossings_iff graph _).mpr
  refine ⟨drawing_crossing_mem_canonicalCrossings
      wellFormed degree isLocal sound.1 sound.2.1
      different (periodNormalize_point_inFundamental graph record)
      proper.1 proper.2.1,
    firstHorizontal⟩

/-- A point already in the fundamental square has zero extracted period
shift. -/
theorem crossingPeriodShift_eq_zero_of_inFundamental
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord)
    (fundamental : InFundamentalDrawingSquare graph record.point) :
    crossingPeriodShift graph record = (0, 0) := by
  have sizePositiveNat : 0 < drawingGridSize graph :=
    drawingGridSize_pos graph
  have sizePositive :
      (0 : Int) < drawingGridSize graph := by
    exact_mod_cast sizePositiveNat
  apply Prod.ext
  · exact Int.ediv_eq_zero_of_lt fundamental.1 fundamental.2.1
  · exact Int.ediv_eq_zero_of_lt fundamental.2.2.1 fundamental.2.2.2

/-- Normalization fixes every canonical oriented crossing record. -/
theorem periodNormalize_eq_self_of_mem_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossings graph) :
    record.periodNormalize graph = record := by
  have canonical :=
    (orientedCrossings_sound graph recordMem).2.2.2.2.1
  have shiftZero :=
    crossingPeriodShift_eq_zero_of_inFundamental
      graph record canonical.1
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  simp [CrossingRecord.periodNormalize, shiftZero,
    PeriodicGridDrawing.normalizePoint,
    PeriodicGridDrawing.periodTranslation,
    Cell.sub, Cell.scale]

/-- Normalizing a genuine halo record a second time has no further effect. -/
theorem periodNormalize_idem_of_mem_orientedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {record : CrossingRecord}
    (recordMem : record ∈ orientedCrossingHalo graph) :
    (record.periodNormalize graph).periodNormalize graph =
      record.periodNormalize graph := by
  exact periodNormalize_eq_self_of_mem_orientedCrossings graph
    (periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal recordMem)

end PeriodicOrthocrossing
end LeanTrominoes

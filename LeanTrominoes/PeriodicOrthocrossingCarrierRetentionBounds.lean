import LeanTrominoes.PeriodicOrthocrossingCarrierTranslationGeometry

/-!
# Bounds for the retained crossing orbit

A neighboring occurrence of a stored segment has both endpoints between
`-2M` and `3M`, where `M` is the drawing period.  Every interior crossing
point on that occurrence has the same bounds, so each coordinate of its
period quotient lies in `{-2, -1, 0, 1, 2}`.  This proves that the `5 × 5`
orbit window used for carrier splitting is large enough around a canonical
owner occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Translating one expanded-square coordinate by a neighboring period keeps
it between `-2M` and `3M`. -/
theorem lane_neighbor_point_in_retention_bounds
    {period base shift point : Int}
    (periodPositive : 0 < period)
    (baseLower : -period < base)
    (baseUpper : base < 2 * period)
    (shiftNeighbor : shift = -1 ∨ shift = 0 ∨ shift = 1)
    (equal : point = base + period * shift) :
    -2 * period < point ∧ point < 3 * period := by
  rcases shiftNeighbor with rfl | rfl | rfl <;> constructor <;> nlinarith

/-- The same bounds hold for a point strictly between two translated
expanded-square coordinates. -/
theorem between_neighbor_point_in_retention_bounds
    {period first last shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (lastLower : -period < last)
    (lastUpper : last < 2 * period)
    (shiftNeighbor : shift = -1 ∨ shift = 0 ∨ shift = 1)
    (between :
      GridSegment.StrictlyBetween
        (first + period * shift)
        (last + period * shift) point) :
    -2 * period < point ∧ point < 3 * period := by
  rcases shiftNeighbor with rfl | rfl | rfl <;>
    unfold GridSegment.StrictlyBetween at between <;>
    rcases between with between | between <;>
    constructor <;> nlinarith

/-- A point lies in the open `5 × 5` drawing-period square centered on the
canonical period. -/
def InCarrierCrossingRetentionSquare
    {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (point : Cell) : Prop :=
  -2 * drawingGridSize graph < point.1 ∧
    point.1 < 3 * drawingGridSize graph ∧
    -2 * drawingGridSize graph < point.2 ∧
    point.2 < 3 * drawingGridSize graph

/-- Every interior point on a neighboring occurrence of a listed drawing
segment lies in the retained `5 × 5` period square. -/
theorem drawing_neighbor_occurrence_point_in_retention_square
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    {translate point : Cell}
    (translateNeighbor : IsNeighborTranslation translate)
    (contains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point) :
    InCarrierCrossingRetentionSquare graph point := by
  have endpointBounds :=
    drawing_indexedSegment_endpoints_inExpandedDrawingSquare
      wellFormed degree isLocal indexedMem
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  rcases endpointBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases translateNeighbor with
    ⟨translateXNeighbor, translateYNeighbor⟩
  rcases contains with
    ⟨_horizontal, pointYEq, pointXBetween⟩ |
      ⟨_vertical, pointXEq, pointYBetween⟩
  · have pointYEq' :
        point.2 =
          indexed.segment.start.2 +
            drawingGridSize graph * translate.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYEq
    have pointXBetween' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.1 +
            drawingGridSize graph * translate.1)
          (indexed.segment.finish.1 +
            drawingGridSize graph * translate.1)
          point.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXBetween
    have xBounds :=
      between_neighbor_point_in_retention_bounds
        periodPositive startXLower startXUpper
        finishXLower finishXUpper translateXNeighbor pointXBetween'
    have yBounds :=
      lane_neighbor_point_in_retention_bounds
        periodPositive startYLower startYUpper
        translateYNeighbor pointYEq'
    exact ⟨xBounds.1, xBounds.2, yBounds.1, yBounds.2⟩
  · have pointXEq' :
        point.1 =
          indexed.segment.start.1 +
            drawingGridSize graph * translate.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXEq
    have pointYBetween' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.2 +
            drawingGridSize graph * translate.2)
          (indexed.segment.finish.2 +
            drawingGridSize graph * translate.2)
          point.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYBetween
    have xBounds :=
      lane_neighbor_point_in_retention_bounds
        periodPositive startXLower startXUpper
        translateXNeighbor pointXEq'
    have yBounds :=
      between_neighbor_point_in_retention_bounds
        periodPositive startYLower startYUpper
        finishYLower finishYUpper translateYNeighbor pointYBetween'
    exact ⟨xBounds.1, xBounds.2, yBounds.1, yBounds.2⟩

/-- Dividing a coordinate in the retained square by the positive period
produces one of the five retained quotient coordinates. -/
theorem periodQuotient_mem_retentionCoordinates
    {period point : Int}
    (periodPositive : 0 < period)
    (pointLower : -2 * period < point)
    (pointUpper : point < 3 * period) :
    point / period ∈ carrierCrossingRetentionCoordinates := by
  have periodNe : period ≠ 0 := ne_of_gt periodPositive
  have remainderNonnegative :=
    Int.emod_nonneg point periodNe
  have remainderLt :=
    Int.emod_lt_of_pos point periodPositive
  have division := Int.emod_add_mul_ediv point period
  have quotientLower : -2 ≤ point / period := by
    by_contra lower
    have quotientLe : point / period ≤ -3 := by omega
    have productLe :
        period * (point / period) ≤ period * (-3) :=
      mul_le_mul_of_nonneg_left quotientLe (le_of_lt periodPositive)
    nlinarith
  have quotientUpper : point / period ≤ 2 := by
    by_contra upper
    have quotientGe : 3 ≤ point / period := by omega
    have productGe :
        period * 3 ≤ period * (point / period) :=
      mul_le_mul_of_nonneg_left quotientGe (le_of_lt periodPositive)
    nlinarith
  rw [mem_carrierCrossingRetentionCoordinates_iff]
  omega

/-- A point in the retained square has a retained two-dimensional period
quotient. -/
theorem crossingPeriodShift_mem_retentionShifts
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord)
    (pointBounds :
      InCarrierCrossingRetentionSquare graph record.point) :
    crossingPeriodShift graph record ∈
      carrierCrossingRetentionShifts := by
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  rw [mem_carrierCrossingRetentionShifts_iff]
  exact
    ⟨(mem_carrierCrossingRetentionCoordinates_iff _).mp
        (periodQuotient_mem_retentionCoordinates
          periodPositive pointBounds.1 pointBounds.2.1),
      (mem_carrierCrossingRetentionCoordinates_iff _).mp
        (periodQuotient_mem_retentionCoordinates
          periodPositive pointBounds.2.2.1 pointBounds.2.2.2)⟩

/-- Normalization followed by restoration of the extracted shift recovers
the original physical crossing record. -/
theorem CrossingRecord.periodNormalize_periodTranslate_shift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) :
    (record.periodNormalize graph).periodTranslate graph
        (crossingPeriodShift graph record) =
      record := by
  rcases record with
    ⟨first, ⟨firstX, firstY⟩,
      second, ⟨secondX, secondY⟩,
      ⟨pointX, pointY⟩⟩
  rcases shiftEq :
      crossingPeriodShift graph
        ({ first := first
           firstTranslate := (firstX, firstY)
           second := second
           secondTranslate := (secondX, secondY)
           point := (pointX, pointY) } : CrossingRecord) with
    ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.periodNormalize, shiftEq,
    PeriodicGridDrawing.normalizePoint,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.sub, Cell.scale, sub_eq_add_neg]

/-- A crossing whose normalization is canonical and whose extracted shift is
retained is explicitly present in the bounded orbit window. -/
theorem mem_retainedCrossings_of_periodNormalize_mem_of_shift_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord)
    (normalizedMem :
      record.periodNormalize graph ∈ orientedCrossings graph)
    (shiftMem :
      crossingPeriodShift graph record ∈
        carrierCrossingRetentionShifts) :
    record ∈ retainedCrossings graph := by
  apply List.mem_flatMap.mpr
  refine ⟨record.periodNormalize graph, normalizedMem, ?_⟩
  apply List.mem_map.mpr
  exact ⟨crossingPeriodShift graph record, shiftMem,
    CrossingRecord.periodNormalize_periodTranslate_shift graph record⟩

end PeriodicOrthocrossing
end LeanTrominoes

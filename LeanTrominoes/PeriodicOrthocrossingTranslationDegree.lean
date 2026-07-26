import LeanTrominoes.PeriodicOrthocrossingHorizontal
import LeanTrominoes.PeriodicOrthocrossingVerticalUnique
import LeanTrominoes.PeriodicOrthocrossingCrossings

/-!
# Degree of translated segment occurrences

A stored route segment has length at most one drawing period along its axis.
Among the nine neighboring translates, at most two copies of that fixed
segment can therefore have an interior point in the half-open fundamental
square.  This is the geometric quotient bound needed when translated terminal
variables are identified during periodicization.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

theorem periodic_shifts_unique_of_values_in_period
    {period base firstShift secondShift firstValue secondValue : Int}
    (periodPositive : 0 < period)
    (firstBounds : 0 ≤ firstValue ∧ firstValue < period)
    (secondBounds : 0 ≤ secondValue ∧ secondValue < period)
    (firstEq : firstValue = base + period * firstShift)
    (secondEq : secondValue = base + period * secondShift) :
    firstShift = secondShift := by
  by_contra shiftsNe
  rcases lt_or_gt_of_ne shiftsNe with shiftsLt | shiftsGt
  · have shiftDifference : 1 ≤ secondShift - firstShift := by omega
    have productDifference :
        period ≤ period * (secondShift - firstShift) := by
      simpa using
        Int.mul_le_mul_of_nonneg_left shiftDifference
          (le_of_lt periodPositive)
    have valueDifference :
        secondValue - firstValue =
          period * (secondShift - firstShift) := by
      rw [firstEq, secondEq]
      ring
    omega
  · have shiftDifference : 1 ≤ firstShift - secondShift := by omega
    have productDifference :
        period ≤ period * (firstShift - secondShift) := by
      simpa using
        Int.mul_le_mul_of_nonneg_left shiftDifference
          (le_of_lt periodPositive)
    have valueDifference :
        firstValue - secondValue =
          period * (firstShift - secondShift) := by
      rw [firstEq, secondEq]
      ring
    omega

theorem opposite_neighbor_shifts_cannot_both_meet
    {period first last firstValue secondValue : Int}
    (spanForward : last - first ≤ period)
    (spanBackward : first - last ≤ period)
    (firstBounds : 0 ≤ firstValue ∧ firstValue < period)
    (secondBounds : 0 ≤ secondValue ∧ secondValue < period)
    (firstBetween :
      GridSegment.StrictlyBetween
        (first - period) (last - period) firstValue)
    (secondBetween :
      GridSegment.StrictlyBetween
        (first + period) (last + period) secondValue) :
    False := by
  unfold GridSegment.StrictlyBetween at firstBetween secondBetween
  rcases firstBetween with firstBetween | firstBetween <;>
    rcases secondBetween with secondBetween | secondBetween <;>
      omega

theorem drawing_indexedSegment_horizontal_span_le_period
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (horizontal : indexed.segment.IsHorizontal) :
    indexed.segment.finish.1 - indexed.segment.start.1 ≤
        drawingGridSize graph ∧
      indexed.segment.start.1 - indexed.segment.finish.1 ≤
        drawingGridSize graph := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨route, routeMem, classified, classifiedMem, indexedEq⟩
  subst indexed
  have edgeMem :
      (route.1.1, route.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx routeMem
  exact classifiedSegment_horizontal_span_le_period
    wellFormed degree edgeMem
      (isLocal route.1.1 (List.fst_mem_of_mem_zipIdx edgeMem))
      (List.fst_mem_of_mem_zipIdx classifiedMem) horizontal

theorem drawing_indexedSegment_vertical_span_le_period
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (vertical : indexed.segment.IsVertical) :
    indexed.segment.finish.2 - indexed.segment.start.2 ≤
        drawingGridSize graph ∧
      indexed.segment.start.2 - indexed.segment.finish.2 ≤
        drawingGridSize graph := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨route, routeMem, classified, classifiedMem, indexedEq⟩
  subst indexed
  have edgeMem :
      (route.1.1, route.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx routeMem
  exact classifiedSegment_vertical_span_le_period
    edgeMem
      (isLocal route.1.1 (List.fst_mem_of_mem_zipIdx edgeMem))
      (List.fst_mem_of_mem_zipIdx classifiedMem) vertical

noncomputable def fundamentalMeetingTranslations
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) : Finset Cell := by
  classical
  exact neighborTranslations.toFinset.filter fun translate =>
    ∃ point,
      InFundamentalDrawingSquare graph point ∧
        (indexed.segment.translate
          ((drawing graph).periodTranslation translate)).InteriorContains
            point

theorem mem_fundamentalMeetingTranslations_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment) (translate : Cell) :
    translate ∈ fundamentalMeetingTranslations graph indexed ↔
      IsNeighborTranslation translate ∧
        ∃ point,
          InFundamentalDrawingSquare graph point ∧
            (indexed.segment.translate
              ((drawing graph).periodTranslation translate)).InteriorContains
                point := by
  classical
  simp [fundamentalMeetingTranslations]

theorem horizontal_meeting_translations_parallel_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (horizontal : indexed.segment.IsHorizontal)
    {firstTranslate secondTranslate firstPoint secondPoint : Cell}
    (firstFundamental :
      InFundamentalDrawingSquare graph firstPoint)
    (secondFundamental :
      InFundamentalDrawingSquare graph secondPoint)
    (firstContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          firstPoint)
    (secondContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          secondPoint) :
    firstTranslate.2 = secondTranslate.2 := by
  have firstHorizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsHorizontal :=
    (GridSegment.isHorizontal_translate indexed.segment
      ((drawing graph).periodTranslation firstTranslate)).mpr horizontal
  have secondHorizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsHorizontal :=
    (GridSegment.isHorizontal_translate indexed.segment
      ((drawing graph).periodTranslation secondTranslate)).mpr horizontal
  have firstLane :
      firstPoint.2 =
        indexed.segment.start.2 +
          drawingGridSize graph * firstTranslate.2 := by
    rcases firstContains with
      ⟨_, pointEq, _⟩ | ⟨vertical, _, _⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointEq
    · exact (firstHorizontal.2 vertical.1).elim
  have secondLane :
      secondPoint.2 =
        indexed.segment.start.2 +
          drawingGridSize graph * secondTranslate.2 := by
    rcases secondContains with
      ⟨_, pointEq, _⟩ | ⟨vertical, _, _⟩
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointEq
    · exact (secondHorizontal.2 vertical.1).elim
  exact periodic_shifts_unique_of_values_in_period
    (by exact_mod_cast drawingGridSize_pos graph)
    ⟨firstFundamental.2.2.1, firstFundamental.2.2.2⟩
    ⟨secondFundamental.2.2.1, secondFundamental.2.2.2⟩
    firstLane secondLane

theorem vertical_meeting_translations_parallel_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (vertical : indexed.segment.IsVertical)
    {firstTranslate secondTranslate firstPoint secondPoint : Cell}
    (firstFundamental :
      InFundamentalDrawingSquare graph firstPoint)
    (secondFundamental :
      InFundamentalDrawingSquare graph secondPoint)
    (firstContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          firstPoint)
    (secondContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          secondPoint) :
    firstTranslate.1 = secondTranslate.1 := by
  have firstVertical :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsVertical :=
    (GridSegment.isVertical_translate indexed.segment
      ((drawing graph).periodTranslation firstTranslate)).mpr vertical
  have secondVertical :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsVertical :=
    (GridSegment.isVertical_translate indexed.segment
      ((drawing graph).periodTranslation secondTranslate)).mpr vertical
  have firstLane :
      firstPoint.1 =
        indexed.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 := by
    rcases firstContains with
      ⟨horizontal, _, _⟩ | ⟨_, pointEq, _⟩
    · exact (firstVertical.2 horizontal.1).elim
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointEq
  have secondLane :
      secondPoint.1 =
        indexed.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 := by
    rcases secondContains with
      ⟨horizontal, _, _⟩ | ⟨_, pointEq, _⟩
    · exact (secondVertical.2 horizontal.1).elim
    · simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointEq
  exact periodic_shifts_unique_of_values_in_period
    (by exact_mod_cast drawingGridSize_pos graph)
    ⟨firstFundamental.1, firstFundamental.2.1⟩
    ⟨secondFundamental.1, secondFundamental.2.1⟩
    firstLane secondLane

theorem horizontal_opposite_neighbor_translations_cannot_both_meet
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (horizontal : indexed.segment.IsHorizontal)
    {firstTranslate secondTranslate firstPoint secondPoint : Cell}
    (firstShift : firstTranslate.1 = -1)
    (secondShift : secondTranslate.1 = 1)
    (firstFundamental :
      InFundamentalDrawingSquare graph firstPoint)
    (secondFundamental :
      InFundamentalDrawingSquare graph secondPoint)
    (firstContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          firstPoint)
    (secondContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          secondPoint) :
    False := by
  have firstHorizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsHorizontal :=
    (GridSegment.isHorizontal_translate indexed.segment
      ((drawing graph).periodTranslation firstTranslate)).mpr horizontal
  have secondHorizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsHorizontal :=
    (GridSegment.isHorizontal_translate indexed.segment
      ((drawing graph).periodTranslation secondTranslate)).mpr horizontal
  have firstBetween :=
    strictlyBetween_x_of_interiorContains_of_isHorizontal
      firstContains firstHorizontal
  have secondBetween :=
    strictlyBetween_x_of_interiorContains_of_isHorizontal
      secondContains secondHorizontal
  have firstBetween' :
      GridSegment.StrictlyBetween
        (indexed.segment.start.1 - drawingGridSize graph)
        (indexed.segment.finish.1 - drawingGridSize graph)
        firstPoint.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, firstShift, sub_eq_add_neg,
      add_comm] using firstBetween
  have secondBetween' :
      GridSegment.StrictlyBetween
        (indexed.segment.start.1 + drawingGridSize graph)
        (indexed.segment.finish.1 + drawingGridSize graph)
        secondPoint.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, secondShift, add_comm] using secondBetween
  have span :=
    drawing_indexedSegment_horizontal_span_le_period
      wellFormed degree isLocal indexedMem horizontal
  exact opposite_neighbor_shifts_cannot_both_meet
    span.1 span.2
    ⟨firstFundamental.1, firstFundamental.2.1⟩
    ⟨secondFundamental.1, secondFundamental.2.1⟩
    firstBetween' secondBetween'

theorem vertical_opposite_neighbor_translations_cannot_both_meet
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (vertical : indexed.segment.IsVertical)
    {firstTranslate secondTranslate firstPoint secondPoint : Cell}
    (firstShift : firstTranslate.2 = -1)
    (secondShift : secondTranslate.2 = 1)
    (firstFundamental :
      InFundamentalDrawingSquare graph firstPoint)
    (secondFundamental :
      InFundamentalDrawingSquare graph secondPoint)
    (firstContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).InteriorContains
          firstPoint)
    (secondContains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).InteriorContains
          secondPoint) :
    False := by
  have firstVertical :
      (indexed.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsVertical :=
    (GridSegment.isVertical_translate indexed.segment
      ((drawing graph).periodTranslation firstTranslate)).mpr vertical
  have secondVertical :
      (indexed.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsVertical :=
    (GridSegment.isVertical_translate indexed.segment
      ((drawing graph).periodTranslation secondTranslate)).mpr vertical
  have firstBetween :=
    strictlyBetween_y_of_interiorContains_of_isVertical
      firstContains firstVertical
  have secondBetween :=
    strictlyBetween_y_of_interiorContains_of_isVertical
      secondContains secondVertical
  have firstBetween' :
      GridSegment.StrictlyBetween
        (indexed.segment.start.2 - drawingGridSize graph)
        (indexed.segment.finish.2 - drawingGridSize graph)
        firstPoint.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, firstShift, sub_eq_add_neg,
      add_comm] using firstBetween
  have secondBetween' :
      GridSegment.StrictlyBetween
        (indexed.segment.start.2 + drawingGridSize graph)
        (indexed.segment.finish.2 + drawingGridSize graph)
        secondPoint.2 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, secondShift, add_comm] using secondBetween
  have span :=
    drawing_indexedSegment_vertical_span_le_period
      isLocal indexedMem vertical
  exact opposite_neighbor_shifts_cannot_both_meet
    span.1 span.2
    ⟨firstFundamental.2.2.1, firstFundamental.2.2.2⟩
    ⟨secondFundamental.2.2.1, secondFundamental.2.2.2⟩
    firstBetween' secondBetween'

theorem fundamentalMeetingTranslations_card_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments) :
    (fundamentalMeetingTranslations graph indexed).card ≤ 2 := by
  classical
  let active := fundamentalMeetingTranslations graph indexed
  change active.card ≤ 2
  by_cases activeEmpty : active = ∅
  · simp [activeEmpty]
  rcases Finset.nonempty_iff_ne_empty.mpr activeEmpty with
    ⟨base, baseMem⟩
  have baseData :=
    (mem_fundamentalMeetingTranslations_iff
      graph indexed base).mp baseMem
  rcases baseData.2 with
    ⟨basePoint, baseFundamental, baseContains⟩
  have axis :=
    drawing_isOrthogonal wellFormed isLocal degree indexed indexedMem
  rcases axis with horizontal | vertical
  · by_cases hasNegative :
        ∃ translate ∈ active, translate.1 = -1
    · rcases hasNegative with
        ⟨negative, negativeMem, negativeShift⟩
      have negativeData :=
        (mem_fundamentalMeetingTranslations_iff
          graph indexed negative).mp negativeMem
      rcases negativeData.2 with
        ⟨negativePoint, negativeFundamental, negativeContains⟩
      calc
        active.card ≤
            ({(-1, base.2), (0, base.2)} : Finset Cell).card := by
          apply Finset.card_le_card
          intro translate translateMem
          rw [Finset.mem_insert, Finset.mem_singleton]
          have translateData :=
            (mem_fundamentalMeetingTranslations_iff
              graph indexed translate).mp translateMem
          rcases translateData.2 with
            ⟨point, fundamental, contains⟩
          have parallel :=
            horizontal_meeting_translations_parallel_eq
              horizontal fundamental baseFundamental
              contains baseContains
          rcases translateData.1.1 with
            shiftNegative | shiftZero | shiftPositive
          · left
            apply Prod.ext
            · exact shiftNegative
            · exact parallel
          · right
            apply Prod.ext
            · exact shiftZero
            · exact parallel
          · exact
              (horizontal_opposite_neighbor_translations_cannot_both_meet
                wellFormed degree isLocal indexedMem horizontal
                negativeShift shiftPositive
                negativeFundamental fundamental
                negativeContains contains).elim
        _ ≤ 2 := Finset.card_le_two
    · calc
        active.card ≤
            ({(0, base.2), (1, base.2)} : Finset Cell).card := by
          apply Finset.card_le_card
          intro translate translateMem
          rw [Finset.mem_insert, Finset.mem_singleton]
          have translateData :=
            (mem_fundamentalMeetingTranslations_iff
              graph indexed translate).mp translateMem
          rcases translateData.2 with
            ⟨point, fundamental, contains⟩
          have parallel :=
            horizontal_meeting_translations_parallel_eq
              horizontal fundamental baseFundamental
              contains baseContains
          rcases translateData.1.1 with
            shiftNegative | shiftZero | shiftPositive
          · exact (hasNegative
              ⟨translate, translateMem, shiftNegative⟩).elim
          · left
            apply Prod.ext
            · exact shiftZero
            · exact parallel
          · right
            apply Prod.ext
            · exact shiftPositive
            · exact parallel
        _ ≤ 2 := Finset.card_le_two
  · by_cases hasNegative :
        ∃ translate ∈ active, translate.2 = -1
    · rcases hasNegative with
        ⟨negative, negativeMem, negativeShift⟩
      have negativeData :=
        (mem_fundamentalMeetingTranslations_iff
          graph indexed negative).mp negativeMem
      rcases negativeData.2 with
        ⟨negativePoint, negativeFundamental, negativeContains⟩
      calc
        active.card ≤
            ({(base.1, -1), (base.1, 0)} : Finset Cell).card := by
          apply Finset.card_le_card
          intro translate translateMem
          rw [Finset.mem_insert, Finset.mem_singleton]
          have translateData :=
            (mem_fundamentalMeetingTranslations_iff
              graph indexed translate).mp translateMem
          rcases translateData.2 with
            ⟨point, fundamental, contains⟩
          have parallel :=
            vertical_meeting_translations_parallel_eq
              vertical fundamental baseFundamental
              contains baseContains
          rcases translateData.1.2 with
            shiftNegative | shiftZero | shiftPositive
          · left
            apply Prod.ext
            · exact parallel
            · exact shiftNegative
          · right
            apply Prod.ext
            · exact parallel
            · exact shiftZero
          · exact
              (vertical_opposite_neighbor_translations_cannot_both_meet
                isLocal indexedMem vertical
                negativeShift shiftPositive
                negativeFundamental fundamental
                negativeContains contains).elim
        _ ≤ 2 := Finset.card_le_two
    · calc
        active.card ≤
            ({(base.1, 0), (base.1, 1)} : Finset Cell).card := by
          apply Finset.card_le_card
          intro translate translateMem
          rw [Finset.mem_insert, Finset.mem_singleton]
          have translateData :=
            (mem_fundamentalMeetingTranslations_iff
              graph indexed translate).mp translateMem
          rcases translateData.2 with
            ⟨point, fundamental, contains⟩
          have parallel :=
            vertical_meeting_translations_parallel_eq
              vertical fundamental baseFundamental
              contains baseContains
          rcases translateData.1.2 with
            shiftNegative | shiftZero | shiftPositive
          · exact (hasNegative
              ⟨translate, translateMem, shiftNegative⟩).elim
          · left
            apply Prod.ext
            · exact parallel
            · exact shiftZero
          · right
            apply Prod.ext
            · exact parallel
            · exact shiftPositive
        _ ≤ 2 := Finset.card_le_two

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.PeriodicContinuousPlanarThreeDM
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-!
# Continuous planarity after degree-two contraction

Every segment of a contracted periodic 3DM route carries provenance naming
an original segment, a lattice shift, and whether its traversal direction
was reversed.  This file uses that provenance to show that degree-two
contraction preserves disjoint continuous route interiors.
-/

namespace LeanTrominoes

namespace GridSegment

@[simp]
theorem reverse_start (segment : GridSegment) :
    segment.reverse.start = segment.finish :=
  rfl

@[simp]
theorem reverse_finish (segment : GridSegment) :
    segment.reverse.finish = segment.start :=
  rfl

/-- Horizontalness is independent of traversal direction. -/
@[simp]
theorem isHorizontal_reverse_iff (segment : GridSegment) :
    segment.reverse.IsHorizontal ↔ segment.IsHorizontal := by
  simp [reverse, IsHorizontal, eq_comm]

/-- Verticalness is independent of traversal direction. -/
@[simp]
theorem isVertical_reverse_iff (segment : GridSegment) :
    segment.reverse.IsVertical ↔ segment.IsVertical := by
  simp [reverse, IsVertical, eq_comm]

/-- Open interval overlap is independent of the order of the first pair
of endpoints. -/
@[simp]
theorem openIntervalsOverlap_swap_left_iff
    (firstStart firstFinish secondStart secondFinish : Int) :
    OpenIntervalsOverlap
        firstFinish firstStart secondStart secondFinish ↔
      OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish := by
  simp [OpenIntervalsOverlap, min_comm, max_comm]

/-- Open interval overlap is independent of the order of the second pair
of endpoints. -/
@[simp]
theorem openIntervalsOverlap_swap_right_iff
    (firstStart firstFinish secondStart secondFinish : Int) :
    OpenIntervalsOverlap
        firstStart firstFinish secondFinish secondStart ↔
      OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish := by
  simp [OpenIntervalsOverlap, min_comm, max_comm]

/-- Strict betweenness is independent of endpoint order. -/
@[simp]
theorem strictlyBetween_swap_iff
    (first finish point : Int) :
    StrictlyBetween finish first point ↔
      StrictlyBetween first finish point := by
  simp [StrictlyBetween, or_comm]

/-- Reversing the first segment does not affect whether two relative
interiors meet. -/
@[simp]
theorem interiorsMeet_reverse_left_iff
    (first second : GridSegment) :
    InteriorsMeet first.reverse second ↔
      InteriorsMeet first second := by
  simp only [InteriorsMeet, isHorizontal_reverse_iff,
    isVertical_reverse_iff, reverse_start, reverse_finish,
    openIntervalsOverlap_swap_left_iff,
    strictlyBetween_swap_iff]
  simp only [IsHorizontal, IsVertical] at *
  aesop

/-- Reversing the second segment does not affect whether two relative
interiors meet. -/
@[simp]
theorem interiorsMeet_reverse_right_iff
    (first second : GridSegment) :
    InteriorsMeet first second.reverse ↔
      InteriorsMeet first second := by
  simp only [InteriorsMeet, isHorizontal_reverse_iff,
    isVertical_reverse_iff, reverse_start, reverse_finish,
    openIntervalsOverlap_swap_right_iff,
    strictlyBetween_swap_iff]
  simp only [IsHorizontal, IsVertical] at *
  aesop

/-- Reversal remains harmless after translating the reversed first
segment. -/
@[simp]
theorem interiorsMeet_translate_reverse_left_iff
    (first second : GridSegment) (offset : Cell) :
    InteriorsMeet (first.reverse.translate offset) second ↔
      InteriorsMeet (first.translate offset) second := by
  rw [← reverse_translate]
  exact interiorsMeet_reverse_left_iff _ _

/-- Reversal remains harmless after translating the reversed second
segment. -/
@[simp]
theorem interiorsMeet_translate_reverse_right_iff
    (first second : GridSegment) (offset : Cell) :
    InteriorsMeet first (second.reverse.translate offset) ↔
      InteriorsMeet first (second.translate offset) := by
  rw [← reverse_translate]
  exact interiorsMeet_reverse_right_iff _ _

end GridSegment

namespace PeriodicThreeDM

/-- Translating two realized contracted segments produces an
interior-intersection exactly when the correspondingly shifted original
segments intersect.  Provenance reversal is geometrically harmless. -/
theorem ContractedSegmentOrigin.realize_translate_interiorsMeet_iff
    (drawing : PeriodicGridDrawing)
    (first second : ContractedSegmentOrigin)
    (firstTranslate secondTranslate : Cell) :
    GridSegment.InteriorsMeet
        ((first.realize drawing).translate
          (drawing.periodTranslation firstTranslate))
        ((second.realize drawing).translate
          (drawing.periodTranslation secondTranslate)) ↔
      GridSegment.InteriorsMeet
        (first.original.segment.translate
          (drawing.periodTranslation
            (Cell.add first.latticeShift firstTranslate)))
        (second.original.segment.translate
          (drawing.periodTranslation
            (Cell.add second.latticeShift secondTranslate))) := by
  rw [first.realize_translate, second.realize_translate]
  split <;> split <;> simp

namespace ContinuousPlanarPresentation

/-- Distinct route occurrences remain continuously interior-disjoint after
degree-two contraction. -/
theorem contractedDrawing_routesHaveDisjointInteriors
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    presentation.contractedDrawing.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent interiorsMeet
  rcases
      presentation.toPlanarPresentation
        |>.contractedIndexedSegment_has_origin firstMember with
    ⟨firstTaggedEdge, firstTaggedOrigin,
      firstEdgeMember, firstOriginMember, firstIndexedEq⟩
  rcases
      presentation.toPlanarPresentation
        |>.contractedIndexedSegment_has_origin secondMember with
    ⟨secondTaggedEdge, secondTaggedOrigin,
      secondEdgeMember, secondOriginMember, secondIndexedEq⟩
  have firstEdgeValueMember :
      firstTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx firstEdgeMember
  have secondEdgeValueMember :
      secondTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx secondEdgeMember
  have firstOriginValueMember :
      firstTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          firstTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx firstOriginMember
  have secondOriginValueMember :
      secondTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          secondTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx secondOriginMember
  have firstOriginalMember :=
    presentation.toPlanarPresentation
      |>.contractedSegmentOrigin_original_mem
        firstEdgeValueMember firstOriginValueMember
  have secondOriginalMember :=
    presentation.toPlanarPresentation
      |>.contractedSegmentOrigin_original_mem
        secondEdgeValueMember secondOriginValueMember
  have originKeysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstTaggedOrigin.1.original
          (Cell.add firstTaggedOrigin.1.latticeShift
            firstTranslate) ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondTaggedOrigin.1.original
          (Cell.add secondTaggedOrigin.1.latticeShift
            secondTranslate) := by
    intro originKeysEqual
    exact keysDifferent
      (presentation.toPlanarPresentation
        |>.contractedOccurrenceKey_eq_of_originKey_eq
          degreeTwoOrThree
          firstEdgeMember secondEdgeMember
          firstOriginMember secondOriginMember
          firstIndexedEq secondIndexedEq
          firstTranslate secondTranslate originKeysEqual)
  have realizedInteriorsMeet :
      GridSegment.InteriorsMeet
        ((firstTaggedOrigin.1.realize presentation.drawing).translate
          (presentation.drawing.periodTranslation firstTranslate))
        ((secondTaggedOrigin.1.realize presentation.drawing).translate
          (presentation.drawing.periodTranslation secondTranslate)) := by
    rw [firstIndexedEq, secondIndexedEq] at interiorsMeet
    simpa using interiorsMeet
  have originalInteriorsMeet :
      GridSegment.InteriorsMeet
        (firstTaggedOrigin.1.original.segment.translate
          (presentation.drawing.periodTranslation
            (Cell.add firstTaggedOrigin.1.latticeShift
              firstTranslate)))
        (secondTaggedOrigin.1.original.segment.translate
          (presentation.drawing.periodTranslation
            (Cell.add secondTaggedOrigin.1.latticeShift
              secondTranslate))) :=
    (firstTaggedOrigin.1.realize_translate_interiorsMeet_iff
      presentation.drawing secondTaggedOrigin.1
      firstTranslate secondTranslate).mp
      realizedInteriorsMeet
  exact
    (presentation.continuouslyPlanar.2
      firstTaggedOrigin.1.original firstOriginalMember
      secondTaggedOrigin.1.original secondOriginalMember
      (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate)
      (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate)
      originKeysDifferent)
      originalInteriorsMeet

/-- Degree-two contraction preserves both integer-grid planarity and exact
continuous route-interior separation. -/
theorem contractedDrawing_isContinuouslyPlanar
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    presentation.contractedDrawing.IsContinuouslyPlanar :=
  ⟨presentation.toPlanarPresentation
      |>.contractedDrawing_isPlanar degreeTwoOrThree,
    presentation.contractedDrawing_routesHaveDisjointInteriors
      degreeTwoOrThree⟩

end ContinuousPlanarPresentation

end PeriodicThreeDM

end LeanTrominoes

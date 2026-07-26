import LeanTrominoes.LocalIncidenceDrawing
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-!
# Continuous planarity for periodic grid drawings

`PeriodicGridDrawing.RoutesAvoidInteriors` detects contacts at integer
points.  That is sufficient for perpendicular crossings and for an endpoint
touching another integer-grid segment, but a coincident pair of unit
segments has intersecting relative interiors with no integer point in that
intersection.

This file records the exact additional condition needed before thickening
or substituting finite gadgets into a periodic drawing.  It uses
`GridSegment.InteriorsMeet`, whose collinear cases compare open integer
intervals directly.  Existing planarity remains part of the strengthened
predicate so endpoint contacts and vertex/route contacts continue to be
excluded.
-/

namespace LeanTrominoes

namespace GridSegment

/-- Common translation preserves overlap of open one-dimensional
intervals. -/
theorem openIntervalsOverlap_add_iff
    (firstStart firstFinish secondStart secondFinish offset : Int) :
    OpenIntervalsOverlap
        (firstStart + offset) (firstFinish + offset)
        (secondStart + offset) (secondFinish + offset) ↔
      OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish := by
  simp [OpenIntervalsOverlap, min_add_add_right, max_add_add_right]

/-- Common translation preserves strict betweenness. -/
theorem strictlyBetween_add_iff
    (first finish point offset : Int) :
    StrictlyBetween (first + offset) (finish + offset) (point + offset) ↔
      StrictlyBetween first finish point := by
  simp [StrictlyBetween]

/-- Translating both segments by the same vector preserves continuous
relative-interior intersection. -/
theorem interiorsMeet_translate_both_iff
    (first second : GridSegment) (offset : Cell) :
    InteriorsMeet (first.translate offset) (second.translate offset) ↔
      InteriorsMeet first second := by
  rcases first with ⟨⟨firstStartX, firstStartY⟩,
    ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with ⟨⟨secondStartX, secondStartY⟩,
    ⟨secondFinishX, secondFinishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [InteriorsMeet, IsHorizontal, IsVertical,
    GridSegment.translate, Cell.add, add_comm,
    openIntervalsOverlap_add_iff, strictlyBetween_add_iff]

end GridSegment

namespace PeriodicGridDrawing

/-- Distinct segment occurrences in the infinite periodic lift have
disjoint continuous relative interiors. -/
def RoutesHaveDisjointInteriors
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedSegments,
    ∀ second ∈ drawing.indexedSegments,
      ∀ firstTranslate secondTranslate,
        SegmentOccurrenceKey first firstTranslate ≠
            SegmentOccurrenceKey second secondTranslate →
          ¬GridSegment.InteriorsMeet
            (first.segment.translate
              (drawing.periodTranslation firstTranslate))
            (second.segment.translate
              (drawing.periodTranslation secondTranslate))

/-- Periodic planarity strong enough for geometric thickening and local
gadget substitution. -/
def IsContinuouslyPlanar
    (drawing : PeriodicGridDrawing) : Prop :=
  drawing.IsPlanar ∧ drawing.RoutesHaveDisjointInteriors

/-- Continuous planarity includes the established integer-grid planarity
interface. -/
theorem IsContinuouslyPlanar.isPlanar
    {drawing : PeriodicGridDrawing}
    (planar : drawing.IsContinuouslyPlanar) :
    drawing.IsPlanar :=
  planar.1

/-- Continuous planarity rules out exact collinear overlap, including
coincident unit segments. -/
theorem IsContinuouslyPlanar.noInteriorsMeet
    {drawing : PeriodicGridDrawing}
    (planar : drawing.IsContinuouslyPlanar)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate : Cell}
    (different :
      SegmentOccurrenceKey first firstTranslate ≠
        SegmentOccurrenceKey second secondTranslate) :
    ¬GridSegment.InteriorsMeet
      (first.segment.translate
        (drawing.periodTranslation firstTranslate))
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)) :=
  planar.2 first firstMember second secondMember
    firstTranslate secondTranslate different

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- A positioned planar incidence presentation with exact continuous
route-interior separation. -/
structure ContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    extends PlanarIncidencePresentation source placement where
  continuouslyPlanar :
    (incidenceDrawing source placement routes).IsContinuouslyPlanar

/-- Anchor normalization changes no drawing data, so it preserves the exact
continuous planarity certificate. -/
def ContinuousPlanarIncidencePresentation.anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      ContinuousPlanarIncidencePresentation source placement) :
    ContinuousPlanarIncidencePresentation
      (source.anchorNormalize placement) placement where
  toPlanarIncidencePresentation :=
    presentation.toPlanarIncidencePresentation.anchorNormalize
  continuouslyPlanar := by
    rw [incidenceDrawing_anchorNormalize]
    exact presentation.continuouslyPlanar

end PositionedPeriodicCNF

end LeanTrominoes

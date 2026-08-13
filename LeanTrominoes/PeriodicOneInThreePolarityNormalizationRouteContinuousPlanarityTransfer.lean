/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSegmentInjectivity

/-!
# Continuous-planarity transfer through polarity-normalized route splitting

Segment provenance and its global injectivity transfer relative-interior
separation from the refined source drawing to the raw split drawing.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Raw route splitting does not change the refined drawing period. -/
@[simp]
theorem rawIncidenceDrawing_periodTranslation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (translate : Cell) :
    (rawIncidenceDrawing presentation).periodTranslation translate =
      (refinedIncidenceDrawing presentation).periodTranslation translate := by
  rfl

/-- Translating a realized raw segment combines its provenance and occurrence
period shifts, up to its harmless traversal reversal. -/
theorem RawSegmentOrigin.realize_translate
    (drawing : PeriodicGridDrawing)
    (origin : RawSegmentOrigin)
    (translate : Cell) :
    (origin.realize drawing).translate
        (drawing.periodTranslation translate) =
      let translated := origin.original.segment.translate
        (drawing.periodTranslation
          (Cell.add origin.latticeShift translate))
      if origin.reversed then translated.reverse else translated := by
  cases reversedEq : origin.reversed
  · simp only [RawSegmentOrigin.realize, reversedEq,
      Bool.false_eq_true, ↓reduceIte]
    rw [PeriodicThreeDM.gridSegment_translate_translate,
      PeriodicThreeDM.periodTranslation_add]
  · simp only [RawSegmentOrigin.realize, reversedEq, ↓reduceIte]
    rw [← GridSegment.reverse_translate,
      PeriodicThreeDM.gridSegment_translate_translate,
      PeriodicThreeDM.periodTranslation_add]

/-- Reversal recorded in provenance does not affect relative-interior
intersection after occurrence translation. -/
theorem RawSegmentOrigin.realize_translate_interiorsMeet_iff
    (drawing : PeriodicGridDrawing)
    (first second : RawSegmentOrigin)
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

/-- Equality of translated refined-source keys forces equality of the raw
segment occurrence keys that produced them. -/
theorem rawOccurrenceKey_eq_of_originKey_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstIncidence secondIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    {firstTaggedOrigin secondTaggedOrigin : RawSegmentOrigin × Nat}
    (firstIncidenceMember :
      firstIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (firstOriginMember :
      firstTaggedOrigin ∈
        (rawSegmentOrigins source sourcePlacement presentation.routes
          firstIncidence.1.clauseIndex
          firstIncidence.1.literalIndex).zipIdx)
    (secondOriginMember :
      secondTaggedOrigin ∈
        (rawSegmentOrigins source sourcePlacement presentation.routes
          secondIncidence.1.clauseIndex
          secondIncidence.1.literalIndex).zipIdx)
    (firstIndexedEq : firstIndexed =
      ⟨firstIncidence.2, firstTaggedOrigin.2,
        firstTaggedOrigin.1.realize
          (refinedIncidenceDrawing presentation)⟩)
    (secondIndexedEq : secondIndexed =
      ⟨secondIncidence.2, secondTaggedOrigin.2,
        secondTaggedOrigin.1.realize
          (refinedIncidenceDrawing presentation)⟩)
    (firstTranslate secondTranslate : Cell)
    (originKeyEq :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstTaggedOrigin.1.original
          (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate) =
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondTaggedOrigin.1.original
          (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate)) :
    PeriodicGridDrawing.SegmentOccurrenceKey firstIndexed firstTranslate =
      PeriodicGridDrawing.SegmentOccurrenceKey
        secondIndexed secondTranslate := by
  simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
    Prod.mk.injEq] at originKeyEq
  rcases originKeyEq with
    ⟨routeIndexEq, segmentIndexEq, translatedEq⟩
  have firstOriginalMember := rawSegmentOrigin_original_mem presentation
    firstIncidenceMember (List.fst_mem_of_mem_zipIdx firstOriginMember)
  have secondOriginalMember := rawSegmentOrigin_original_mem presentation
    secondIncidenceMember (List.fst_mem_of_mem_zipIdx secondOriginMember)
  have originalEq :
      firstTaggedOrigin.1.original = secondTaggedOrigin.1.original :=
    PeriodicThreeDM.indexedSegment_eq_of_indices_eq
      (refinedIncidenceDrawing presentation)
      firstOriginalMember secondOriginalMember routeIndexEq segmentIndexEq
  have provenanceEq := rawSegmentOrigins_global_injective presentation
    firstIncidenceMember secondIncidenceMember
    firstOriginMember secondOriginMember originalEq
  have firstIncidenceEq := provenanceEq.1
  have firstOriginEq := provenanceEq.2
  subst secondIncidence
  subst secondTaggedOrigin
  have translateEq : firstTranslate = secondTranslate := by
    rcases firstTaggedOrigin.1.latticeShift with ⟨shiftX, shiftY⟩
    rcases firstTranslate with ⟨firstX, firstY⟩
    rcases secondTranslate with ⟨secondX, secondY⟩
    simp only [Cell.add, Prod.mk.injEq] at translatedEq ⊢
    omega
  subst secondTranslate
  rw [firstIndexedEq, secondIndexedEq]

/-- The raw split drawing inherits continuous relative-interior separation
from the refined source drawing. -/
theorem rawIncidenceDrawing_routesHaveDisjointInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (rawIncidenceDrawing presentation).RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent interiorsMeet
  rcases rawIndexedSegment_has_origin presentation firstMember with
    ⟨firstIncidence, firstTaggedOrigin,
      firstIncidenceMember, firstOriginMember, firstIndexedEq⟩
  rcases rawIndexedSegment_has_origin presentation secondMember with
    ⟨secondIncidence, secondTaggedOrigin,
      secondIncidenceMember, secondOriginMember, secondIndexedEq⟩
  have firstOriginalMember := rawSegmentOrigin_original_mem presentation
    firstIncidenceMember (List.fst_mem_of_mem_zipIdx firstOriginMember)
  have secondOriginalMember := rawSegmentOrigin_original_mem presentation
    secondIncidenceMember (List.fst_mem_of_mem_zipIdx secondOriginMember)
  have originKeysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstTaggedOrigin.1.original
          (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate) ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondTaggedOrigin.1.original
          (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate) := by
    intro originKeysEqual
    exact keysDifferent
      (rawOccurrenceKey_eq_of_originKey_eq presentation
        firstIncidenceMember secondIncidenceMember
        firstOriginMember secondOriginMember
        firstIndexedEq secondIndexedEq
        firstTranslate secondTranslate originKeysEqual)
  have realizedInteriorsMeet :
      GridSegment.InteriorsMeet
        ((firstTaggedOrigin.1.realize
            (refinedIncidenceDrawing presentation)).translate
          ((refinedIncidenceDrawing presentation).periodTranslation
            firstTranslate))
        ((secondTaggedOrigin.1.realize
            (refinedIncidenceDrawing presentation)).translate
          ((refinedIncidenceDrawing presentation).periodTranslation
            secondTranslate)) := by
    rw [firstIndexedEq, secondIndexedEq] at interiorsMeet
    simpa using interiorsMeet
  have originalInteriorsMeet :
      GridSegment.InteriorsMeet
        (firstTaggedOrigin.1.original.segment.translate
          ((refinedIncidenceDrawing presentation).periodTranslation
            (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate)))
        (secondTaggedOrigin.1.original.segment.translate
          ((refinedIncidenceDrawing presentation).periodTranslation
            (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate))) :=
    (firstTaggedOrigin.1.realize_translate_interiorsMeet_iff
      (refinedIncidenceDrawing presentation) secondTaggedOrigin.1
      firstTranslate secondTranslate).mp realizedInteriorsMeet
  exact
    ((refinedRouteFamily_isContinuouslyPlanar presentation).2
      firstTaggedOrigin.1.original firstOriginalMember
      secondTaggedOrigin.1.original secondOriginalMember
      (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate)
      (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate)
      originKeysDifferent)
      originalInteriorsMeet

/-- The raw split drawing is continuously planar. -/
theorem rawIncidenceDrawing_isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (rawIncidenceDrawing presentation).IsContinuouslyPlanar :=
  ⟨by
      apply PeriodicGridDrawing.isPlanar_of_hasUnitSteps
      simpa [rawIncidenceDrawing] using
        rawIncidenceDrawing_hasUnitSteps presentation,
    rawIncidenceDrawing_routesHaveDisjointInteriors presentation⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes

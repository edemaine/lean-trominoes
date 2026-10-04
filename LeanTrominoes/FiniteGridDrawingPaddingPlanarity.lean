/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteGridDrawingPadding
import LeanTrominoes.FundamentalGridDrawingSeparation

/-! # Padding a finite drawing preserves exact continuous planarity -/
namespace LeanTrominoes.PeriodicGridDrawing

private theorem sub_zero_eq {first second : Cell} (zero : Cell.sub first second=(0,0)) : first=second := by
  apply Prod.ext
  · have eq := congrArg Prod.fst zero; simp only [Cell.sub] at eq; omega
  · have eq := congrArg Prod.snd zero; simp only [Cell.sub] at eq; omega

theorem finitePad_routesAvoidInteriors {drawing : PeriodicGridDrawing}
    (bounds : drawing.SegmentEndpointsInExpandedSquare) (avoids : drawing.RoutesAvoidInteriors) :
    drawing.finitePad.RoutesAvoidInteriors := by
  intro first firstMember second secondMember firstTranslate secondTranslate point different contains other
  have translateEq := sub_zero_eq (relativeTranslate_eq_zero_of_contact
    (finitePad_segmentEndpoints bounds) firstMember secondMember contains other)
  subst secondTranslate
  obtain ⟨originalFirst,originalFirstMember,firstEq⟩ := List.mem_map.mp
    (by simpa only [finitePad_indexedSegments] using firstMember)
  obtain ⟨originalSecond,originalSecondMember,secondEq⟩ := List.mem_map.mp
    (by simpa only [finitePad_indexedSegments] using secondMember)
  subst first second
  let common := Cell.add drawing.finitePaddingOffset (drawing.finitePad.periodTranslation firstTranslate)
  let originalPoint := Cell.sub point common
  have pointEq : Cell.add originalPoint common=point := by simp [originalPoint,Cell.sub,Cell.add]
  have firstSegmentEq : ((drawing.finitePadIndexed originalFirst).segment.translate
      (drawing.finitePad.periodTranslation firstTranslate))=originalFirst.segment.translate common := by
    apply congrArg₂ GridSegment.mk <;> apply Prod.ext <;> simp [finitePadIndexed,common,GridSegment.translate,Cell.add] <;> ring
  have secondSegmentEq : ((drawing.finitePadIndexed originalSecond).segment.translate
      (drawing.finitePad.periodTranslation firstTranslate))=originalSecond.segment.translate common := by
    apply congrArg₂ GridSegment.mk <;> apply Prod.ext <;> simp [finitePadIndexed,common,GridSegment.translate,Cell.add] <;> ring
  rw [firstSegmentEq,← pointEq,interiorContains_translate_iff] at contains
  rw [secondSegmentEq,← pointEq,contains_translate_iff] at other
  have originalDifferent : SegmentOccurrenceKey originalFirst (0,0)≠SegmentOccurrenceKey originalSecond (0,0) := by
    simpa [SegmentOccurrenceKey,finitePadIndexed] using different
  apply avoids originalFirst originalFirstMember originalSecond originalSecondMember (0,0) (0,0) originalPoint originalDifferent
  · simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using contains
  · simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using other

theorem finitePad_routesHaveDisjointInteriors {drawing : PeriodicGridDrawing}
    (bounds : drawing.SegmentEndpointsInExpandedSquare) (avoids : drawing.RoutesHaveDisjointInteriors) :
    drawing.finitePad.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember firstTranslate secondTranslate different meet
  have translateEq := sub_zero_eq (relativeTranslate_eq_zero_of_interiorsMeet
    (finitePad_segmentEndpoints bounds) firstMember secondMember meet)
  subst secondTranslate
  have meetBase := (GridSegment.interiorsMeet_translate_both_iff first.segment second.segment
    (drawing.finitePad.periodTranslation firstTranslate)).mp meet
  obtain ⟨originalFirst,originalFirstMember,firstEq⟩ := List.mem_map.mp
    (by simpa only [finitePad_indexedSegments] using firstMember)
  obtain ⟨originalSecond,originalSecondMember,secondEq⟩ := List.mem_map.mp
    (by simpa only [finitePad_indexedSegments] using secondMember)
  subst first second
  have meetOriginal := (GridSegment.interiorsMeet_translate_both_iff originalFirst.segment originalSecond.segment
    drawing.finitePaddingOffset).mp meetBase
  have originalDifferent : SegmentOccurrenceKey originalFirst (0,0)≠SegmentOccurrenceKey originalSecond (0,0) := by
    simpa [SegmentOccurrenceKey,finitePadIndexed] using different
  apply avoids originalFirst originalFirstMember originalSecond originalSecondMember (0,0) (0,0) originalDifferent
  simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using meetOriginal

theorem finitePad_verticesAvoidRouteInteriors {drawing : PeriodicGridDrawing}
    (bounds : drawing.SegmentEndpointsInExpandedSquare)
    (vertexBounds : ∀ point∈drawing.vertexPositions,drawing.PositionInFundamentalSquare point)
    (avoids : drawing.VerticesAvoidRouteInteriors) : drawing.finitePad.VerticesAvoidRouteInteriors := by
  intro vertex vertexMember indexed indexedMember vertexTranslate routeTranslate contains
  have vertexInside : drawing.finitePad.PositionInFundamentalSquare vertex := by
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp vertexMember
    exact finitePad_point_inFundamental (positionInExpandedSquare_of_fundamental (vertexBounds _ originalMember))
  have normalized : (indexed.segment.translate
      (drawing.finitePad.periodTranslation (Cell.sub routeTranslate vertexTranslate))).InteriorContains vertex := by
    simpa [normalizePoint,Cell.add,Cell.sub] using
      (interiorContains_normalize drawing.finitePad indexed.segment routeTranslate vertexTranslate
        (Cell.add vertex (drawing.finitePad.periodTranslation vertexTranslate))).mp contains
  have translateEq := sub_zero_eq (occurrence_translate_eq_zero_of_contact
    (finitePad_segmentEndpoints bounds indexed indexedMember) vertexInside normalized)
  subst routeTranslate
  obtain ⟨originalVertex,originalVertexMember,vertexEq⟩ := List.mem_map.mp vertexMember
  obtain ⟨originalIndexed,originalIndexedMember,indexedEq⟩ := List.mem_map.mp
    (by simpa only [finitePad_indexedSegments] using indexedMember)
  subst vertex indexed
  have baseContains : originalIndexed.segment.InteriorContains originalVertex := by
    have normalizedBase : (drawing.finitePadIndexed originalIndexed).segment.InteriorContains
        (Cell.add drawing.finitePaddingOffset originalVertex) := by
      simpa [Cell.sub,periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using normalized
    rw [show Cell.add drawing.finitePaddingOffset originalVertex=Cell.add originalVertex drawing.finitePaddingOffset by
      simp [Cell.add,add_comm]] at normalizedBase
    exact (interiorContains_translate_iff _ _ _).mp normalizedBase
  apply avoids originalVertex originalVertexMember originalIndexed originalIndexedMember (0,0) (0,0)
  simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using baseContains

theorem finitePad_isContinuouslyPlanar {drawing : PeriodicGridDrawing}
    (bounds : drawing.SegmentEndpointsInExpandedSquare)
    (vertexBounds : ∀ point∈drawing.vertexPositions,drawing.PositionInFundamentalSquare point)
    (planar : drawing.IsContinuouslyPlanar) : drawing.finitePad.IsContinuouslyPlanar :=
  ⟨⟨finitePad_routesAvoidInteriors bounds planar.1.1,
    finitePad_verticesAvoidRouteInteriors bounds vertexBounds planar.1.2⟩,
    finitePad_routesHaveDisjointInteriors bounds planar.2⟩
end LeanTrominoes.PeriodicGridDrawing

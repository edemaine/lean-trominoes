/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingGeometryComputability
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability
import LeanTrominoes.PeriodicOrthocrossingCrossingHalo

/-!
# Computability of the retained crossing halo

The finite `3 × 3` block of translated segment occurrences and every proper
horizontal/vertical crossing among them are primitive recursive from the
source periodic graph.  This is the crossover-site enumeration used by the
retained planar SAT construction.
-/

noncomputable section

namespace LeanTrominoes

namespace GridSegment

theorem properlyCrossesAt_primrec :
    PrimrecPred fun input : (GridSegment × GridSegment) × Cell =>
      ProperlyCrossesAt input.1.1 input.1.2 input.2 := by
  have firstContains : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.1.InteriorContains input.2 :=
    interiorContains_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have secondContains : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.2.InteriorContains input.2 :=
    interiorContains_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have firstHorizontal : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.1.IsHorizontal :=
    isHorizontal_primrec.comp (Primrec.fst.comp Primrec.fst)
  have firstVertical : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.1.IsVertical :=
    isVertical_primrec.comp (Primrec.fst.comp Primrec.fst)
  have secondHorizontal : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.2.IsHorizontal :=
    isHorizontal_primrec.comp (Primrec.snd.comp Primrec.fst)
  have secondVertical : PrimrecPred fun input :
      (GridSegment × GridSegment) × Cell =>
      input.1.2.IsVertical :=
    isVertical_primrec.comp (Primrec.snd.comp Primrec.fst)
  exact firstContains.and (secondContains.and
    ((firstHorizontal.and secondVertical).or
      (firstVertical.and secondHorizontal)))

end GridSegment

namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

namespace CrossingRecord

def equivData : CrossingRecord ≃
    (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell) × Cell where
  toFun record :=
    ((record.first, record.firstTranslate),
      (record.second, record.secondTranslate), record.point)
  invFun data :=
    ⟨data.1.1, data.1.2, data.2.1.1, data.2.1.2, data.2.2⟩
  left_inv record := by cases record; rfl
  right_inv data := by
    rcases data with ⟨⟨first, firstTranslate⟩,
      ⟨⟨second, secondTranslate⟩, point⟩⟩
    rfl

noncomputable instance : Primcodable CrossingRecord :=
  Primcodable.ofEquiv
    ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell) × Cell) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem first_primrec : Primrec CrossingRecord.first :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem firstTranslate_primrec :
    Primrec CrossingRecord.firstTranslate :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem second_primrec : Primrec CrossingRecord.second :=
  ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem secondTranslate_primrec :
    Primrec CrossingRecord.secondTranslate :=
  ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem point_primrec : Primrec CrossingRecord.point :=
  ((Primrec.snd.comp Primrec.snd).comp equivData_primrec).of_eq
    fun _ => rfl

theorem mk_primrec : Primrec fun data :
    (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell) × Cell =>
    CrossingRecord.mk data.1.1 data.1.2
      data.2.1.1 data.2.1.2 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end CrossingRecord

theorem neighborOccurrences_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (neighborOccurrences : PeriodicGraph Vertex →
      List (IndexedGridSegment × Cell)) := by
  have segments : Primrec fun graph : PeriodicGraph Vertex =>
      (drawing graph).indexedSegments :=
    PeriodicGridDrawing.indexedSegments_primrec.comp drawing_primrec
  exact (Primrec.list_flatMap segments
    (Primrec.list_map (Primrec.const neighborTranslations)
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).of_eq
          fun _ => rfl

theorem CrossingRecord.firstSegment_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CrossingRecord.firstSegment :
      PeriodicGraph Vertex → CrossingRecord → GridSegment) := by
  change Primrec fun input : PeriodicGraph Vertex × CrossingRecord =>
    input.2.firstSegment input.1
  have segment : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      input.2.first.segment :=
    IndexedGridSegment.segment_primrec.comp
      (CrossingRecord.first_primrec.comp Primrec.snd)
  have translation : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      (drawing input.1).periodTranslation input.2.firstTranslate :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      (drawing_primrec.comp Primrec.fst)
      (CrossingRecord.firstTranslate_primrec.comp Primrec.snd)
  exact (GridSegment.translate_primrec.comp translation segment).of_eq
    fun _ => rfl

theorem CrossingRecord.secondSegment_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CrossingRecord.secondSegment :
      PeriodicGraph Vertex → CrossingRecord → GridSegment) := by
  change Primrec fun input : PeriodicGraph Vertex × CrossingRecord =>
    input.2.secondSegment input.1
  have segment : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      input.2.second.segment :=
    IndexedGridSegment.segment_primrec.comp
      (CrossingRecord.second_primrec.comp Primrec.snd)
  have translation : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      (drawing input.1).periodTranslation input.2.secondTranslate :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      (drawing_primrec.comp Primrec.fst)
      (CrossingRecord.secondTranslate_primrec.comp Primrec.snd)
  exact (GridSegment.translate_primrec.comp translation segment).of_eq
    fun _ => rfl

theorem orientedIntersectionPoint_primrec :
    Primrec₂ orientedIntersectionPoint := by
  unfold orientedIntersectionPoint
  exact Primrec.pair
    ((Primrec.fst.comp GridSegment.start_primrec).comp₂
      Primrec₂.right)
    ((Primrec.snd.comp GridSegment.start_primrec).comp₂
      Primrec₂.left)

theorem orientedCrossingCandidate_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input :
        (PeriodicGraph Vertex × (IndexedGridSegment × Cell)) ×
          (IndexedGridSegment × Cell) =>
      orientedCrossingCandidate input.1.1 input.1.2 input.2 := by
  let Input :=
    (PeriodicGraph Vertex × (IndexedGridSegment × Cell)) ×
      (IndexedGridSegment × Cell)
  have firstSegment : Primrec fun input : Input => GridSegment.translate
      ((drawing input.1.1).periodTranslation input.1.2.2)
      input.1.2.1.segment := by
    exact GridSegment.translate_primrec.comp
      (PeriodicGridDrawing.periodTranslation_primrec.comp
        (drawing_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (IndexedGridSegment.segment_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  have secondSegment : Primrec fun input : Input => GridSegment.translate
      ((drawing input.1.1).periodTranslation input.2.2)
      input.2.1.segment := by
    exact GridSegment.translate_primrec.comp
      (PeriodicGridDrawing.periodTranslation_primrec.comp
        (drawing_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
      (IndexedGridSegment.segment_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  have point : Primrec fun input : Input =>
      orientedIntersectionPoint
        (GridSegment.translate
          ((drawing input.1.1).periodTranslation input.1.2.2)
          input.1.2.1.segment)
        (GridSegment.translate
          ((drawing input.1.1).periodTranslation input.2.2)
          input.2.1.segment) :=
    orientedIntersectionPoint_primrec.comp firstSegment secondSegment
  exact (CrossingRecord.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)) point))).of_eq fun _ => rfl

theorem crossingHaloCandidates_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (crossingHaloCandidates :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have occurrences := neighborOccurrences_primrec (Vertex := Vertex)
  have inner : Primrec₂ fun
      (input : PeriodicGraph Vertex × (IndexedGridSegment × Cell))
      (second : IndexedGridSegment × Cell) =>
      orientedCrossingCandidate input.1 input.2 second := by
    exact orientedCrossingCandidate_primrec
  have row : Primrec₂ fun (graph : PeriodicGraph Vertex)
      (first : IndexedGridSegment × Cell) =>
      (neighborOccurrences graph).map fun second =>
        orientedCrossingCandidate graph first second := by
    change Primrec fun input :
        PeriodicGraph Vertex × (IndexedGridSegment × Cell) =>
      (neighborOccurrences input.1).map fun second =>
        orientedCrossingCandidate input.1 input.2 second
    exact Primrec.list_map
      (occurrences.comp Primrec.fst) inner
  exact (Primrec.list_flatMap occurrences row).of_eq fun _ => rfl

theorem crossingRecordIsInCrossingHalo_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    PrimrecRel fun (graph : PeriodicGraph Vertex) (record : CrossingRecord) =>
      record.IsInCrossingHalo graph := by
  change PrimrecPred fun input : PeriodicGraph Vertex × CrossingRecord =>
    input.2.IsInCrossingHalo input.1
  have firstKey : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        input.2.first input.2.firstTranslate :=
    PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
      (CrossingRecord.first_primrec.comp Primrec.snd)
      (CrossingRecord.firstTranslate_primrec.comp Primrec.snd)
  have secondKey : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        input.2.second input.2.secondTranslate :=
    PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
      (CrossingRecord.second_primrec.comp Primrec.snd)
      (CrossingRecord.secondTranslate_primrec.comp Primrec.snd)
  have different : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      PeriodicGridDrawing.SegmentOccurrenceKey
          input.2.first input.2.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          input.2.second input.2.secondTranslate :=
    (Primrec.eq.comp firstKey secondKey).not
  have firstSegment : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      input.2.firstSegment input.1 :=
    CrossingRecord.firstSegment_primrec
  have secondSegment : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      input.2.secondSegment input.1 :=
    CrossingRecord.secondSegment_primrec
  have firstHorizontal : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      (input.2.firstSegment input.1).IsHorizontal :=
    GridSegment.isHorizontal_primrec.comp firstSegment
  have secondVertical : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      (input.2.secondSegment input.1).IsVertical :=
    GridSegment.isVertical_primrec.comp secondSegment
  have proper : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      GridSegment.ProperlyCrossesAt
        (input.2.firstSegment input.1)
        (input.2.secondSegment input.1) input.2.point :=
    GridSegment.properlyCrossesAt_primrec.comp
      (Primrec.pair
        (Primrec.pair firstSegment secondSegment)
        (CrossingRecord.point_primrec.comp Primrec.snd))
  exact different.and
    (firstHorizontal.and (secondVertical.and proper))

theorem orientedCrossingHalo_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (orientedCrossingHalo :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have inHalo : PrimrecRel fun (record : CrossingRecord)
      (graph : PeriodicGraph Vertex) => record.IsInCrossingHalo graph :=
    crossingRecordIsInCrossingHalo_primrec.comp₂
      Primrec₂.right Primrec₂.left
  have filtered : Primrec fun graph : PeriodicGraph Vertex =>
      (crossingHaloCandidates graph).filter fun record =>
        record.IsInCrossingHalo graph :=
    inHalo.listFilter.comp
      crossingHaloCandidates_primrec Primrec.id
  exact PeriodicThreeSATThree.dedup_primrec.comp filtered

theorem orientedCrossingHalo_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (orientedCrossingHalo :
      PeriodicGraph Vertex → List CrossingRecord) :=
  orientedCrossingHalo_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

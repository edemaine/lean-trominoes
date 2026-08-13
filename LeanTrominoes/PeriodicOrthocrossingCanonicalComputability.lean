/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingHaloComputability

/-!
# Computability of canonical orthocrossings

The canonical fundamental-square enumeration and its horizontal-first
orientation are primitive recursive.  This supplies the canonical crossover
representatives used by the retained carrier construction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

theorem fundamentalCoordinates_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (fundamentalCoordinates :
      PeriodicGraph Vertex → List Int) := by
  unfold fundamentalCoordinates
  exact Primrec.list_map
    (Primrec.list_range.comp drawingGridSize_primrec)
    (Computability.int_ofNat_primrec.comp Primrec.snd).to₂

theorem fundamentalPoints_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (fundamentalPoints :
      PeriodicGraph Vertex → List Cell) := by
  have coordinates :=
    fundamentalCoordinates_primrec (Vertex := Vertex)
  have row : Primrec₂ fun (graph : PeriodicGraph Vertex)
      (horizontal : Int) =>
      (fundamentalCoordinates graph).map fun vertical =>
        (horizontal, vertical) := by
    change Primrec fun input : PeriodicGraph Vertex × Int =>
      (fundamentalCoordinates input.1).map fun vertical =>
        (input.2, vertical)
    exact Primrec.list_map
      (coordinates.comp Primrec.fst)
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_flatMap coordinates row).of_eq fun _ => rfl

theorem inFundamentalDrawingSquare_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    PrimrecRel fun (graph : PeriodicGraph Vertex) (point : Cell) =>
      InFundamentalDrawingSquare graph point := by
  change PrimrecPred fun input : PeriodicGraph Vertex × Cell =>
    0 ≤ input.2.1 ∧
      input.2.1 < drawingGridSize input.1 ∧
      0 ≤ input.2.2 ∧
      input.2.2 < drawingGridSize input.1
  have size : Primrec fun input : PeriodicGraph Vertex × Cell =>
      (drawingGridSize input.1 : Int) :=
    Computability.int_ofNat_primrec.comp
      (drawingGridSize_primrec.comp Primrec.fst)
  exact (Computability.int_le_primrec.comp
    (Primrec.const (0 : Int)) (Primrec.fst.comp Primrec.snd)).and
    ((Computability.int_lt_primrec.comp
      (Primrec.fst.comp Primrec.snd) size).and
    ((Computability.int_le_primrec.comp
      (Primrec.const (0 : Int)) (Primrec.snd.comp Primrec.snd)).and
      (Computability.int_lt_primrec.comp
        (Primrec.snd.comp Primrec.snd) size)))

theorem crossingCandidates_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (crossingCandidates :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have occurrences := neighborOccurrences_primrec (Vertex := Vertex)
  have points := fundamentalPoints_primrec (Vertex := Vertex)
  have pointCandidates : Primrec fun input :
      (PeriodicGraph Vertex × (IndexedGridSegment × Cell)) ×
        (IndexedGridSegment × Cell) =>
      (fundamentalPoints input.1.1).map fun point =>
        CrossingRecord.mk input.1.2.1 input.1.2.2
          input.2.1 input.2.2 point := by
    exact Primrec.list_map
      (points.comp (Primrec.fst.comp Primrec.fst))
      (CrossingRecord.mk_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp
              (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.fst.comp Primrec.fst))))
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))).to₂
  have secondCandidates : Primrec₂ fun
      (input : PeriodicGraph Vertex × (IndexedGridSegment × Cell))
      (second : IndexedGridSegment × Cell) =>
      (fundamentalPoints input.1).map fun point =>
        CrossingRecord.mk input.2.1 input.2.2
          second.1 second.2 point := by
    exact pointCandidates
  have row : Primrec₂ fun (graph : PeriodicGraph Vertex)
      (first : IndexedGridSegment × Cell) =>
      (neighborOccurrences graph).flatMap fun second =>
        (fundamentalPoints graph).map fun point =>
          CrossingRecord.mk first.1 first.2
            second.1 second.2 point := by
    change Primrec fun input :
        PeriodicGraph Vertex × (IndexedGridSegment × Cell) =>
      (neighborOccurrences input.1).flatMap fun second =>
        (fundamentalPoints input.1).map fun point =>
          CrossingRecord.mk input.2.1 input.2.2
            second.1 second.2 point
    exact Primrec.list_flatMap
      (occurrences.comp Primrec.fst) secondCandidates
  exact (Primrec.list_flatMap occurrences row).of_eq fun _ => rfl

theorem crossingRecordIsCanonical_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    PrimrecRel fun (graph : PeriodicGraph Vertex) (record : CrossingRecord) =>
      record.IsCanonical graph := by
  change PrimrecPred fun input : PeriodicGraph Vertex × CrossingRecord =>
    input.2.IsCanonical input.1
  have fundamental : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      InFundamentalDrawingSquare input.1 input.2.point :=
    inFundamentalDrawingSquare_primrec.comp
      Primrec.fst (CrossingRecord.point_primrec.comp Primrec.snd)
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
  have proper : PrimrecPred fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      GridSegment.ProperlyCrossesAt
        (input.2.firstSegment input.1)
        (input.2.secondSegment input.1) input.2.point :=
    GridSegment.properlyCrossesAt_primrec.comp
      (Primrec.pair
        (Primrec.pair firstSegment secondSegment)
        (CrossingRecord.point_primrec.comp Primrec.snd))
  exact fundamental.and (different.and proper)

theorem canonicalCrossings_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (canonicalCrossings :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have canonical : PrimrecRel fun (record : CrossingRecord)
      (graph : PeriodicGraph Vertex) => record.IsCanonical graph :=
    crossingRecordIsCanonical_primrec.comp₂
      Primrec₂.right Primrec₂.left
  exact canonical.listFilter.comp crossingCandidates_primrec Primrec.id

theorem orientedCrossings_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (orientedCrossings :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have horizontal : PrimrecRel fun (record : CrossingRecord)
      (graph : PeriodicGraph Vertex) =>
      (record.firstSegment graph).IsHorizontal := by
    change PrimrecPred fun input :
      CrossingRecord × PeriodicGraph Vertex =>
        (input.1.firstSegment input.2).IsHorizontal
    exact GridSegment.isHorizontal_primrec.comp
      (CrossingRecord.firstSegment_primrec.comp
        Primrec.snd Primrec.fst)
  have filtered : Primrec fun graph : PeriodicGraph Vertex =>
      (canonicalCrossings graph).filter fun record =>
        (record.firstSegment graph).IsHorizontal :=
    horizontal.listFilter.comp canonicalCrossings_primrec Primrec.id
  exact PeriodicThreeSATThree.dedup_primrec.comp filtered

theorem orientedCrossings_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (orientedCrossings :
      PeriodicGraph Vertex → List CrossingRecord) :=
  orientedCrossings_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

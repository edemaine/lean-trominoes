/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCanonicalShiftData
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingHaloSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRetentionBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedBoundaryGeometry
import LeanTrominoes.ListFilterMapUnique
import LeanTrominoes.ListDedupMapDedup

/-! # Semantics of fixed common-shift crossing candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Subtracting a common occurrence shift translates the reconstructed
crossing record by the corresponding negative period shift. -/
theorem occurrencePairCrossingRecordAtPeriod_subtractShift
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    occurrencePairCrossingRecordAtPeriod period
        (occurrencePairSubtractShift pair shift) =
      crossingRecordPeriodTranslateAtPeriod period
        (occurrencePairCrossingRecordAtPeriod period pair)
        (Cell.sub (0, 0) shift) := by
  rw [crossingRecordPeriodTranslateAtPeriod_occurrencePairCrossingRecord]
  rcases pair with ⟨⟨first, ⟨firstX, firstY⟩⟩,
    ⟨second, ⟨secondX, secondY⟩⟩⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [occurrencePairSubtractShift, Cell.add, Cell.sub,
    sub_eq_add_neg]

/-- Subtracting the reconstructed point quotient is the explicit numeric
normalization of the crossing record. -/
theorem occurrencePairCrossingRecordAtPeriod_subtract_periodShift
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    occurrencePairCrossingRecordAtPeriod period
        (occurrencePairSubtractShift pair
          (crossingRecordPeriodShiftAtPeriod period
            (occurrencePairCrossingRecordAtPeriod period pair))) =
      crossingRecordPeriodNormalizeAtPeriod period
        (occurrencePairCrossingRecordAtPeriod period pair) := by
  rw [occurrencePairCrossingRecordAtPeriod_subtractShift]
  rcases occurrencePairCrossingRecordAtPeriod period pair with
    ⟨first, ⟨firstX, firstY⟩, second, ⟨secondX, secondY⟩,
      ⟨pointX, pointY⟩⟩
  rcases shiftEq :
      crossingRecordPeriodShiftAtPeriod period
        ({ first := first
           firstTranslate := (firstX, firstY)
           second := second
           secondTranslate := (secondX, secondY)
           point := (pointX, pointY) } : CrossingRecord) with
    ⟨shiftX, shiftY⟩
  simp [crossingRecordPeriodTranslateAtPeriod,
    crossingRecordPeriodNormalizeAtPeriod, shiftEq,
    Cell.add, Cell.sub, Cell.scale, sub_eq_add_neg]

/-- Canonicality together with horizontal-first orientation is exactly a
fundamental-square restriction of the physical halo predicate. -/
theorem crossingRecord_isCanonical_horizontal_iff_inFundamental_isInHalo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    (record.IsCanonical graph ∧
        (record.firstSegment graph).IsHorizontal) ↔
      InFundamentalDrawingSquare graph record.point ∧
        record.IsInCrossingHalo graph := by
  constructor
  · rintro ⟨⟨fundamental, different, proper⟩, firstHorizontal⟩
    have secondVertical :
        (record.secondSegment graph).IsVertical := by
      rcases proper.2.2 with horizontalVertical | verticalHorizontal
      · exact horizontalVertical.2
      · exact False.elim
          (firstHorizontal.2 verticalHorizontal.1.1)
    exact ⟨fundamental, different, firstHorizontal,
      secondVertical, proper⟩
  · rintro ⟨fundamental, different, firstHorizontal,
      secondVertical, proper⟩
    exact ⟨⟨fundamental, different, proper⟩, firstHorizontal⟩

/-- A common period translation preserves the physical horizontal-first
crossing predicate. -/
theorem CrossingRecord.isInCrossingHalo_periodTranslate_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord)
    (shift : Cell) :
    (record.periodTranslate graph shift).IsInCrossingHalo graph ↔
      record.IsInCrossingHalo graph := by
  let offset := (drawing graph).periodTranslation shift
  rw [CrossingRecord.IsInCrossingHalo,
    CrossingRecord.IsInCrossingHalo]
  rw [show (record.periodTranslate graph shift).firstSegment graph =
      (record.firstSegment graph).translate offset by
        exact CrossingRecord.firstSegment_periodTranslate graph record shift]
  rw [show (record.periodTranslate graph shift).secondSegment graph =
      (record.secondSegment graph).translate offset by
        exact CrossingRecord.secondSegment_periodTranslate graph record shift]
  simp only [CrossingRecord.periodTranslate,
    GridSegment.ProperlyCrossesAt,
    GridSegment.translate_isHorizontal_iff,
    GridSegment.translate_isVertical_iff]
  rw [PeriodicGridDrawing.interiorContains_translate_iff,
    PeriodicGridDrawing.interiorContains_translate_iff]
  constructor
  · rintro ⟨different, horizontal, vertical, firstContains,
      secondContains, axes⟩
    refine ⟨?_, horizontal, vertical, firstContains,
      secondContains, axes⟩
    intro equal
    apply different
    simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
      Prod.mk.injEq] at equal ⊢
    exact ⟨equal.1, equal.2.1,
      congrArg (fun cell => Cell.add cell shift) equal.2.2⟩
  · rintro ⟨different, horizontal, vertical, firstContains,
      secondContains, axes⟩
    refine ⟨?_, horizontal, vertical, firstContains,
      secondContains, axes⟩
    intro equal
    apply different
    simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
      Prod.mk.injEq] at equal ⊢
    exact ⟨equal.1, equal.2.1,
      Cell.add_right_injective shift equal.2.2⟩

/-- Exactly the extracted point quotient translates a physical crossing
point into the canonical half-open fundamental square. -/
theorem CrossingRecord.periodTranslate_neg_point_inFundamental_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord)
    (shift : Cell) :
    InFundamentalDrawingSquare graph
        (record.periodTranslate graph (Cell.sub (0, 0) shift)).point ↔
      crossingPeriodShift graph record = shift := by
  constructor
  · intro fundamental
    have zero := crossingPeriodShift_eq_zero_of_inFundamental graph
      (record.periodTranslate graph (Cell.sub (0, 0) shift)) fundamental
    rw [crossingPeriodShift_periodTranslate] at zero
    rcases quotientEq : crossingPeriodShift graph record with
      ⟨quotientX, quotientY⟩
    rcases shift with ⟨shiftX, shiftY⟩
    simp [Cell.add, Cell.sub, quotientEq] at zero ⊢
    omega
  · intro shiftEq
    have fundamental := periodNormalize_point_inFundamental graph record
    have pointEq :
        (record.periodTranslate graph (Cell.sub (0, 0) shift)).point =
          (record.periodNormalize graph).point := by
      rcases record with
        ⟨first, firstTranslate, second, secondTranslate, point⟩
      simp only [CrossingRecord.periodTranslate,
        CrossingRecord.periodNormalize]
      rw [shiftEq]
      rcases crossingPeriodShift graph
          ({ first := first
             firstTranslate := firstTranslate
             second := second
             secondTranslate := secondTranslate
             point := point } : CrossingRecord) with
        ⟨shiftX, shiftY⟩
      rcases point with ⟨pointX, pointY⟩
      simp [PeriodicGridDrawing.normalizePoint,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.sub, Cell.scale, sub_eq_add_neg]
    rw [pointEq]
    exact fundamental

/-- Among common shifts, the canonical predicate accepts exactly the point's
period quotient, provided the original pair is a physical halo crossing. -/
theorem canonicalOrientedOccurrencePairAtPeriod_subtractShift_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    canonicalOrientedOccurrencePairAtPeriod
        (drawingGridSize graph)
        (occurrencePairSubtractShift pair shift) = true ↔
      orientedOccurrencePairInCrossingHaloAtPeriod
          (drawingGridSize graph) pair = true ∧
        crossingRecordPeriodShiftAtPeriod
            (drawingGridSize graph)
            (occurrencePairCrossingRecordAtPeriod
              (drawingGridSize graph) pair) = shift := by
  let record := orientedCrossingCandidate graph pair.1 pair.2
  have shiftedRecordEq :
      orientedCrossingCandidate graph
          (occurrencePairSubtractShift pair shift).1
          (occurrencePairSubtractShift pair shift).2 =
        record.periodTranslate graph (Cell.sub (0, 0) shift) := by
    rw [← occurrencePairCrossingRecordAtPeriod_drawingGridSize,
      occurrencePairCrossingRecordAtPeriod_subtractShift,
      crossingRecordPeriodTranslateAtPeriod_drawingGridSize,
      occurrencePairCrossingRecordAtPeriod_drawingGridSize]
  rw [← canonicalOrientedOccurrencePair_eq_atPeriod graph]
  unfold canonicalOrientedOccurrencePair
  rw [decide_eq_true_eq,
    crossingRecord_isCanonical_horizontal_iff_inFundamental_isInHalo,
    shiftedRecordEq,
    CrossingRecord.periodTranslate_neg_point_inFundamental_iff,
    CrossingRecord.isInCrossingHalo_periodTranslate_iff]
  rw [orientedOccurrencePairInCrossingHaloAtPeriod_drawingGridSize]
  rw [decide_eq_true_eq]
  rw [crossingRecordPeriodShiftAtPeriod_drawingGridSize]
  constructor <;> rintro ⟨first, second⟩ <;>
    exact ⟨second, first⟩

/-- A genuine physical halo pair contributes exactly its one normalized
crossing record to the fixed twenty-five-shift block. -/
theorem occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_singleton
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (halo : orientedOccurrencePairInCrossingHaloAtPeriod
      (drawingGridSize graph) pair = true)
    (shiftMem :
      crossingRecordPeriodShiftAtPeriod
          (drawingGridSize graph)
          (occurrencePairCrossingRecordAtPeriod
            (drawingGridSize graph) pair) ∈
        carrierCrossingRetentionShifts) :
    occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
        (drawingGridSize graph) pair =
      [crossingRecordPeriodNormalizeAtPeriod
        (drawingGridSize graph)
        (occurrencePairCrossingRecordAtPeriod
          (drawingGridSize graph) pair)] := by
  let period := drawingGridSize graph
  let quotient := crossingRecordPeriodShiftAtPeriod period
    (occurrencePairCrossingRecordAtPeriod period pair)
  let normalized := crossingRecordPeriodNormalizeAtPeriod period
    (occurrencePairCrossingRecordAtPeriod period pair)
  unfold occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
    occurrencePairCanonicalShiftCandidatesAtPeriod
  rw [List.filterMap_map]
  calc
    carrierCrossingRetentionShifts.filterMap
        (Option.map (occurrencePairCrossingRecordAtPeriod period) ∘
          occurrencePairCanonicalShiftCandidateAtPeriod period pair) =
      carrierCrossingRetentionShifts.filterMap (fun shift =>
        if shift = quotient then some normalized else none) := by
          apply List.filterMap_congr
          intro shift _shiftMember
          by_cases same : shift = quotient
          · subst shift
            have accepted :
                canonicalOrientedOccurrencePairAtPeriod period
                    (occurrencePairSubtractShift pair quotient) = true :=
              (canonicalOrientedOccurrencePairAtPeriod_subtractShift_iff
                graph pair quotient).mpr ⟨halo, rfl⟩
            simp only [Function.comp_apply,
              occurrencePairCanonicalShiftCandidateAtPeriod,
              accepted, if_true, Option.map_some]
            simpa [quotient, normalized] using
              occurrencePairCrossingRecordAtPeriod_subtract_periodShift
                period pair
          · have rejected :
                canonicalOrientedOccurrencePairAtPeriod period
                    (occurrencePairSubtractShift pair shift) = false := by
              apply Bool.eq_false_of_not_eq_true
              intro accepted
              exact same
                ((canonicalOrientedOccurrencePairAtPeriod_subtractShift_iff
                  graph pair shift).mp accepted).2.symm
            simp [occurrencePairCanonicalShiftCandidateAtPeriod,
              rejected, same]
    _ = [normalized] :=
      List.filterMap_eq_singleton_of_nodup
        carrierCrossingRetentionShifts quotient normalized
        carrierCrossingRetentionShifts_nodup shiftMem

/-- Neighbor-occurrence bounds guarantee that every genuine physical pair's
unique normalizing quotient is one of the twenty-five compiled shifts. -/
theorem occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_singleton_of_neighbor_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (firstMem : pair.1 ∈ neighborOccurrences graph)
    (halo : orientedOccurrencePairInCrossingHaloAtPeriod
      (drawingGridSize graph) pair = true) :
    occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
        (drawingGridSize graph) pair =
      [crossingRecordPeriodNormalizeAtPeriod
        (drawingGridSize graph)
        (occurrencePairCrossingRecordAtPeriod
          (drawingGridSize graph) pair)] := by
  have firstData := (mem_neighborOccurrences_iff graph pair.1).mp firstMem
  have haloSemantic :
      (orientedCrossingCandidate graph pair.1 pair.2).IsInCrossingHalo
        graph := by
    have haloDecision := halo
    rw [orientedOccurrencePairInCrossingHaloAtPeriod_drawingGridSize,
      decide_eq_true_eq] at haloDecision
    exact haloDecision
  have pointBounds :
      InCarrierCrossingRetentionSquare graph
        (orientedCrossingCandidate graph pair.1 pair.2).point :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal firstData.1 firstData.2
      haloSemantic.2.2.2.1
  have semanticShiftMem := crossingPeriodShift_mem_retentionShifts graph
    (orientedCrossingCandidate graph pair.1 pair.2) pointBounds
  have numericShiftMem :
      crossingRecordPeriodShiftAtPeriod
          (drawingGridSize graph)
          (occurrencePairCrossingRecordAtPeriod
            (drawingGridSize graph) pair) ∈
        carrierCrossingRetentionShifts := by
    rw [crossingRecordPeriodShiftAtPeriod_drawingGridSize,
      occurrencePairCrossingRecordAtPeriod_drawingGridSize]
    exact semanticShiftMem
  exact
    occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_singleton
      graph pair halo numericShiftMem

/-- The compact source-key projection of a genuine physical pair is likewise
a singleton containing its normalized canonical-left boundary identity. -/
theorem occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod_eq_singleton_of_neighbor_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (firstMem : pair.1 ∈ neighborOccurrences graph)
    (halo : orientedOccurrencePairInCrossingHaloAtPeriod
      (drawingGridSize graph) pair = true) :
    occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
        (drawingGridSize graph) pair =
      [RetainedCompactAtomWords.crossingPair
        (crossingRecordPeriodNormalizeAtPeriod
          (drawingGridSize graph)
          (occurrencePairCrossingRecordAtPeriod
            (drawingGridSize graph) pair))] := by
  unfold occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
  rw [occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_singleton_of_neighbor_mem
    wellFormed degree isLocal pair firstMem halo]
  rfl

/-- A noncrossing physical pair activates no common-shift candidate. -/
theorem occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_nil_of_not_halo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (notHalo : orientedOccurrencePairInCrossingHaloAtPeriod
      (drawingGridSize graph) pair = false) :
    occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
        (drawingGridSize graph) pair = [] := by
  unfold occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
    occurrencePairCanonicalShiftCandidatesAtPeriod
  rw [List.filterMap_map, List.filterMap_eq_nil_iff]
  intro shift _shiftMember
  have rejected :
      canonicalOrientedOccurrencePairAtPeriod
          (drawingGridSize graph)
          (occurrencePairSubtractShift pair shift) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro accepted
    have halo :=
      (canonicalOrientedOccurrencePairAtPeriod_subtractShift_iff
        graph pair shift).mp accepted |>.1
    rw [notHalo] at halo
    contradiction
  simp [occurrencePairCanonicalShiftCandidateAtPeriod, rejected]

/-- On a neighboring physical pair, the fixed block is exactly the optional
singleton presentation of physical-halo filtering and normalization. -/
theorem occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_if
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (firstMem : pair.1 ∈ neighborOccurrences graph) :
    occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
        (drawingGridSize graph) pair =
      if orientedOccurrencePairInCrossingHaloAtPeriod
          (drawingGridSize graph) pair then
        [crossingRecordPeriodNormalizeAtPeriod
          (drawingGridSize graph)
          (occurrencePairCrossingRecordAtPeriod
            (drawingGridSize graph) pair)]
      else
        [] := by
  by_cases halo : orientedOccurrencePairInCrossingHaloAtPeriod
      (drawingGridSize graph) pair = true
  · rw [occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_singleton_of_neighbor_mem
      wellFormed degree isLocal pair firstMem halo]
    simp [halo]
  · have notHalo := Bool.eq_false_of_not_eq_true halo
    rw [occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_nil_of_not_halo
      graph pair notHalo]
    simp [notHalo]

/-- Concatenating the fixed blocks over the physical occurrence square gives
exactly the physical halo filter mapped through numeric normalization. -/
theorem occurrencePairCanonicalCrossingRecordShiftScanAtPeriod_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph) =
      (occurrencePairCrossingHaloAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph)).map fun pair =>
          crossingRecordPeriodNormalizeAtPeriod
            (drawingGridSize graph)
            (occurrencePairCrossingRecordAtPeriod
              (drawingGridSize graph) pair) := by
  unfold occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
    occurrencePairCrossingHaloAtPeriod
  apply List.flatMap_eq_filter_map_of_eq_if
  intro pair pairMem
  have firstMem : pair.1 ∈ neighborOccurrences graph :=
    (List.mem_product.mp pairMem).1
  exact occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod_eq_if
    wellFormed degree isLocal pair firstMem

/-- Stable deduplication of the compiled physical shift scan is the exact
graph-free canonicalized crossing-halo presentation. -/
theorem occurrencePairCanonicalCrossingRecordShiftScanAtPeriod_dedup_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    (occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
      (drawingGridSize graph) (neighborOccurrences graph)).dedup =
        occurrencePairCanonicalizedCrossingHaloAtPeriod
          (drawingGridSize graph) (neighborOccurrences graph) := by
  rw [occurrencePairCanonicalCrossingRecordShiftScanAtPeriod_eq
    wellFormed degree isLocal]
  rfl

/-- Deduplicating the compact source-pair scan agrees with mapping the exact
canonical crossing presentation and deduplicating only possible key
collisions. -/
theorem occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph) =
      ((occurrencePairCanonicalizedCrossingHaloAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph)).map
          RetainedCompactAtomWords.crossingPair).dedup := by
  unfold occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod
    occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod
  rw [← List.dedup_map_dedup,
    occurrencePairCanonicalCrossingRecordShiftScanAtPeriod_dedup_eq
      wellFormed degree isLocal]

end LeanTrominoes.PeriodicOrthocrossing

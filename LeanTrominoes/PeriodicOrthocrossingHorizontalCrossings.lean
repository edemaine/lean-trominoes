/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicOrthocrossingCanonical
import LeanTrominoes.PeriodicOrthocrossingHorizontalBounds

/-!
# Crossing translations in horizontal orthocrossing drawings

An occurrence of a segment whose stored endpoints lie strictly inside one
vertical period can meet the canonical vertical band only at vertical
translate zero.  Thus every canonical crossing of a horizontal source has
zero vertical translation on both participating segment occurrences.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Open-band route-point bounds specialize to both endpoints of any indexed
route segment. -/
theorem RoutePointsInOpenVerticalBand.indexedSegment
    {drawing : PeriodicGridDrawing}
    (bounded : drawing.RoutePointsInOpenVerticalBand)
    {indexed : IndexedGridSegment}
    (indexedMember : indexed ∈ drawing.indexedSegments) :
    (0 < indexed.segment.start.2 ∧
        indexed.segment.start.2 < drawing.gridSize) ∧
      (0 < indexed.segment.finish.2 ∧
        indexed.segment.finish.2 < drawing.gridSize) := by
  simp only [PeriodicGridDrawing.indexedSegments, List.mem_flatMap]
    at indexedMember
  obtain ⟨taggedRoute, taggedRouteMember, indexedMember⟩ := indexedMember
  simp only [List.mem_map] at indexedMember
  obtain ⟨taggedSegment, taggedSegmentMember, rfl⟩ := indexedMember
  have routeMember : taggedRoute.1 ∈ drawing.edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMember
  have segmentMember : taggedSegment.1 ∈
      gridPolylineSegments taggedRoute.1 :=
    List.fst_mem_of_mem_zipIdx taggedSegmentMember
  have endpoints := gridPolylineSegments_endpoints_mem segmentMember
  exact ⟨bounded taggedRoute.1 routeMember _ endpoints.1,
    bounded taggedRoute.1 routeMember _ endpoints.2⟩

/-- Translating an open-band segment occurrence into contact with the
canonical band forces its vertical period translate to be zero. -/
theorem verticalTranslate_eq_zero_of_interiorContains
    {drawing : PeriodicGridDrawing}
    {segment : GridSegment} {translate point : Cell}
    (startBounds :
      0 < segment.start.2 ∧ segment.start.2 < drawing.gridSize)
    (finishBounds :
      0 < segment.finish.2 ∧ segment.finish.2 < drawing.gridSize)
    (pointBounds :
      0 ≤ point.2 ∧ point.2 < drawing.gridSize)
    (contains :
      (segment.translate
        (drawing.periodTranslation translate)).InteriorContains point) :
    translate.2 = 0 := by
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have periodNonnegative : (0 : Int) ≤ drawing.gridSize :=
    periodPositive.le
  rcases lt_trichotomy translate.2 0 with negative | zero | positive
  · have translateLe : translate.2 ≤ -1 := by omega
    have productLe :
        (drawing.gridSize : Int) * translate.2 ≤
          (drawing.gridSize : Int) * (-1) :=
      Int.mul_le_mul_of_nonneg_left translateLe periodNonnegative
    simp only [GridSegment.InteriorContains, GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale]
      at contains
    rcases contains with
      ⟨_, pointEqual, _⟩ | ⟨_, _, between⟩
    · omega
    · unfold GridSegment.StrictlyBetween at between
      rcases between with between | between <;> omega
  · exact zero
  · have translateGe : 1 ≤ translate.2 := by omega
    have productGe :
        (drawing.gridSize : Int) * 1 ≤
          (drawing.gridSize : Int) * translate.2 :=
      Int.mul_le_mul_of_nonneg_left translateGe periodNonnegative
    simp only [GridSegment.InteriorContains, GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale]
      at contains
    rcases contains with
      ⟨_, pointEqual, _⟩ | ⟨_, _, between⟩
    · omega
    · unfold GridSegment.StrictlyBetween at between
      rcases between with between | between <;> omega

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

/-- Both segment occurrences at every canonical oriented crossing of a
horizontal local graph use vertical translate zero. -/
theorem orientedCrossing_verticalTranslations_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {record : CrossingRecord}
    (recordMember : record ∈ orientedCrossings graph) :
    record.firstTranslate.2 = 0 ∧ record.secondTranslate.2 = 0 := by
  have sound := orientedCrossings_sound graph recordMember
  have canonical := sound.2.2.2.2.1
  have routeBounds :=
    drawing_routePointsInOpenVerticalBand isLocal horizontal
  have firstBounds := routeBounds.indexedSegment sound.1
  have secondBounds := routeBounds.indexedSegment sound.2.1
  have pointBounds :
      0 ≤ record.point.2 ∧
        record.point.2 < (drawing graph).gridSize := by
    simpa [InFundamentalDrawingSquare, drawing_gridSize] using
      ⟨canonical.1.2.2.1, canonical.1.2.2.2⟩
  exact ⟨
    PeriodicGridDrawing.verticalTranslate_eq_zero_of_interiorContains
      firstBounds.1 firstBounds.2 pointBounds canonical.2.2.1,
    PeriodicGridDrawing.verticalTranslate_eq_zero_of_interiorContains
      secondBounds.1 secondBounds.2 pointBounds canonical.2.2.2.1⟩

/-- In the larger physical crossing halo, both participating occurrences
have the same vertical translate as the crossing point's extracted common
period shift. -/
theorem orientedCrossingHalo_verticalTranslations_eq_shift
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets)
    {record : CrossingRecord}
    (recordMember : record ∈ orientedCrossingHalo graph) :
    record.firstTranslate.2 = (crossingPeriodShift graph record).2 ∧
      record.secondTranslate.2 = (crossingPeriodShift graph record).2 := by
  have normalizedMember :=
    periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal recordMember
  have normalizedZero :=
    orientedCrossing_verticalTranslations_eq_zero
      isLocal horizontal normalizedMember
  have firstReconstruction := congrArg Prod.snd
    (periodNormalize_firstTranslate_add_shift graph record)
  have secondReconstruction := congrArg Prod.snd
    (periodNormalize_secondTranslate_add_shift graph record)
  simp only [Cell.add] at firstReconstruction secondReconstruction
  constructor <;> omega

end PeriodicOrthocrossing
end LeanTrominoes

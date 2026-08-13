/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCorrectionEndpoints
import LeanTrominoes.PeriodicOrthocrossingCarrierCoordinateOrder

/-!
# Strict order for retained carrier boundaries

The retained crossing window contains period translates of canonical
crossings.  This file transfers the two geometric facts needed to sort those
extra boundary ports: their horizontal and vertical occurrences keep their
axes, and a physical occurrence together with the crossing point determines
the entire retained crossing record.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A retained oriented crossing still has a horizontal first occurrence and
a vertical second occurrence. -/
theorem retainedCrossing_firstHorizontal_secondVertical
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ retainedCrossings graph) :
    (record.firstSegment graph).IsHorizontal ∧
      (record.secondSegment graph).IsVertical := by
  rcases List.mem_flatMap.mp recordMem with
    ⟨canonical, canonicalMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨shift, _shiftMem, recordEq⟩
  rw [← recordEq, CrossingRecord.firstSegment_periodTranslate,
    CrossingRecord.secondSegment_periodTranslate]
  have sound :=
    orientedCrossingHalo_sound graph
      (orientedCrossings_subset_orientedCrossingHalo
        graph canonicalMem)
  exact
    ⟨(GridSegment.isHorizontal_translate _ _).mpr
        sound.2.2.2.2.2.1,
      (GridSegment.isVertical_translate _ _).mpr
        sound.2.2.2.2.2.2.1⟩

/-- Normalizing a retained crossing gives one of the canonical oriented
crossings. -/
theorem retainedCrossing_periodNormalize_mem_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ retainedCrossings graph) :
    record.periodNormalize graph ∈ orientedCrossings graph := by
  rcases List.mem_flatMap.mp recordMem with
    ⟨canonical, canonicalMem, translatedMem⟩
  rcases List.mem_map.mp translatedMem with
    ⟨shift, _shiftMem, recordEq⟩
  rw [← recordEq,
    CrossingRecord.periodNormalize_periodTranslate,
    periodNormalize_eq_self_of_mem_orientedCrossings
      graph canonicalMem]
  exact canonicalMem

/-- Retained crossings sharing their horizontal occurrence and crossing
point are the same physical crossing record. -/
theorem retainedCrossing_eq_of_firstOccurrence_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ retainedCrossings graph)
    (secondMem : second ∈ retainedCrossings graph)
    (firstIndexedEqual : first.first = second.first)
    (firstTranslateEqual :
      first.firstTranslate = second.firstTranslate)
    (pointEqual : first.point = second.point) :
    first = second := by
  have shiftEqual :
      crossingPeriodShift graph first =
        crossingPeriodShift graph second := by
    simp [crossingPeriodShift, pointEqual]
  have normalizedFirstIndexed :
      (first.periodNormalize graph).first =
        (second.periodNormalize graph).first := by
    simpa [CrossingRecord.periodNormalize] using firstIndexedEqual
  have normalizedFirstTranslate :
      (first.periodNormalize graph).firstTranslate =
        (second.periodNormalize graph).firstTranslate := by
    simp [CrossingRecord.periodNormalize,
      firstTranslateEqual, shiftEqual]
  have normalizedPoint :
      (first.periodNormalize graph).point =
        (second.periodNormalize graph).point := by
    simp only [CrossingRecord.periodNormalize]
    rw [pointEqual, shiftEqual]
  have normalizedEqual :=
    orientedCrossing_eq_of_firstOccurrence_eq_of_point_eq
      wellFormed degree isLocal
      (orientedCrossings_subset_orientedCrossingHalo graph
        (retainedCrossing_periodNormalize_mem_orientedCrossings
          graph firstMem))
      (orientedCrossings_subset_orientedCrossingHalo graph
        (retainedCrossing_periodNormalize_mem_orientedCrossings
          graph secondMem))
      normalizedFirstIndexed normalizedFirstTranslate normalizedPoint
  rw [← CrossingRecord.periodNormalize_periodTranslate_shift
      graph first,
    ← CrossingRecord.periodNormalize_periodTranslate_shift
      graph second,
    normalizedEqual, shiftEqual]

/-- Retained crossings sharing their vertical occurrence and crossing point
are the same physical crossing record. -/
theorem retainedCrossing_eq_of_secondOccurrence_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ retainedCrossings graph)
    (secondMem : second ∈ retainedCrossings graph)
    (secondIndexedEqual : first.second = second.second)
    (secondTranslateEqual :
      first.secondTranslate = second.secondTranslate)
    (pointEqual : first.point = second.point) :
    first = second := by
  have shiftEqual :
      crossingPeriodShift graph first =
        crossingPeriodShift graph second := by
    simp [crossingPeriodShift, pointEqual]
  have normalizedSecondIndexed :
      (first.periodNormalize graph).second =
        (second.periodNormalize graph).second := by
    simpa [CrossingRecord.periodNormalize] using secondIndexedEqual
  have normalizedSecondTranslate :
      (first.periodNormalize graph).secondTranslate =
        (second.periodNormalize graph).secondTranslate := by
    simp [CrossingRecord.periodNormalize,
      secondTranslateEqual, shiftEqual]
  have normalizedPoint :
      (first.periodNormalize graph).point =
        (second.periodNormalize graph).point := by
    simp only [CrossingRecord.periodNormalize]
    rw [pointEqual, shiftEqual]
  have normalizedEqual :=
    orientedCrossing_eq_of_secondOccurrence_eq_of_point_eq
      wellFormed degree isLocal
      (orientedCrossings_subset_orientedCrossingHalo graph
        (retainedCrossing_periodNormalize_mem_orientedCrossings
          graph firstMem))
      (orientedCrossings_subset_orientedCrossingHalo graph
        (retainedCrossing_periodNormalize_mem_orientedCrossings
          graph secondMem))
      normalizedSecondIndexed normalizedSecondTranslate normalizedPoint
  rw [← CrossingRecord.periodNormalize_periodTranslate_shift
      graph first,
    ← CrossingRecord.periodNormalize_periodTranslate_shift
      graph second,
    normalizedEqual, shiftEqual]

/-- Crossing points on one retained horizontal occurrence have the same
second coordinate. -/
theorem retainedCrossing_point_snd_eq_of_firstOccurrence_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CrossingRecord}
    (firstMem : first ∈ retainedCrossings graph)
    (secondMem : second ∈ retainedCrossings graph)
    (indexedEqual : first.first = second.first)
    (translateEqual :
      first.firstTranslate = second.firstTranslate) :
    first.point.2 = second.point.2 := by
  have firstSound := retainedCrossings_sound graph firstMem
  have secondSound := retainedCrossings_sound graph secondMem
  have firstAxes :=
    retainedCrossing_firstHorizontal_secondVertical graph firstMem
  have secondAxes :=
    retainedCrossing_firstHorizontal_secondVertical graph secondMem
  have firstCoordinate :=
    GridSegment.snd_eq_start_of_interiorContains_horizontal
      firstSound.2.2.1 firstAxes.1
  have secondCoordinate :=
    GridSegment.snd_eq_start_of_interiorContains_horizontal
      secondSound.2.2.1 secondAxes.1
  simp [CrossingRecord.firstSegment,
    indexedEqual, translateEqual] at firstCoordinate
  exact firstCoordinate.trans secondCoordinate.symm

/-- Crossing points on one retained vertical occurrence have the same first
coordinate. -/
theorem retainedCrossing_point_fst_eq_of_secondOccurrence_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CrossingRecord}
    (firstMem : first ∈ retainedCrossings graph)
    (secondMem : second ∈ retainedCrossings graph)
    (indexedEqual : first.second = second.second)
    (translateEqual :
      first.secondTranslate = second.secondTranslate) :
    first.point.1 = second.point.1 := by
  have firstSound := retainedCrossings_sound graph firstMem
  have secondSound := retainedCrossings_sound graph secondMem
  have firstAxes :=
    retainedCrossing_firstHorizontal_secondVertical graph firstMem
  have secondAxes :=
    retainedCrossing_firstHorizontal_secondVertical graph secondMem
  have firstCoordinate :=
    GridSegment.fst_eq_start_of_interiorContains_vertical
      firstSound.2.2.2.1 firstAxes.2
  have secondCoordinate :=
    GridSegment.fst_eq_start_of_interiorContains_vertical
      secondSound.2.2.2.1 secondAxes.2
  simp [CrossingRecord.secondSegment,
    indexedEqual, translateEqual] at firstCoordinate
  exact firstCoordinate.trans secondCoordinate.symm

/-- Distinct retained crossover sites on one carrier never share the same
refined order coordinate. -/
theorem retainedCrossingBoundary_orderCoordinate_ne_of_common_carrier
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingBoundary}
    (firstMem : first ∈ retainedCrossingBoundaries graph)
    (secondMem : second ∈ retainedCrossingBoundaries graph)
    (keyEqual : first.carrierKey = second.carrierKey)
    (crossingDifferent : first.crossing ≠ second.crossing) :
    (CarrierNode.boundary first).orderCoordinate graph ≠
      (CarrierNode.boundary second).orderCoordinate graph := by
  have firstData :=
    retainedCrossingBoundary_indexed_mem_and_contains
      graph firstMem
  have secondData :=
    retainedCrossingBoundary_indexed_mem_and_contains
      graph secondMem
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (first := CarrierNode.boundary first)
      (second := CarrierNode.boundary second)
      firstData.1 secondData.1
      (by simpa [CarrierNode.carrierKey] using keyEqual)
  have firstCrossingMem :=
    retainedCrossingBoundary_crossing_mem graph firstMem
  have secondCrossingMem :=
    retainedCrossingBoundary_crossing_mem graph secondMem
  have firstAxes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph firstCrossingMem
  have secondAxes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph secondCrossingMem
  intro coordinateEqual
  cases first with
  | mk firstCrossing firstSide =>
      cases second with
      | mk secondCrossing secondSide =>
          cases firstSide <;> cases secondSide
          · have pointSndEqual :=
              retainedCrossing_point_snd_eq_of_firstOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointFstEqual :
                firstCrossing.point.1 =
                  secondCrossing.point.1 := by
              change
                20 * firstCrossing.point.1 + 1 =
                  20 * secondCrossing.point.1 + 1
                at coordinateEqual
              omega
            exact crossingDifferent
              (retainedCrossing_eq_of_firstOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · change
              20 * firstCrossing.point.1 + 1 =
                20 * secondCrossing.point.1 + 11
              at coordinateEqual
            omega
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp firstAxes.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp secondAxes.2
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp firstAxes.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp secondAxes.2
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · change
              20 * firstCrossing.point.1 + 11 =
                20 * secondCrossing.point.1 + 1
              at coordinateEqual
            omega
          · have pointSndEqual :=
              retainedCrossing_point_snd_eq_of_firstOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointFstEqual :
                firstCrossing.point.1 =
                  secondCrossing.point.1 := by
              change
                20 * firstCrossing.point.1 + 11 =
                  20 * secondCrossing.point.1 + 11
                at coordinateEqual
              omega
            exact crossingDifferent
              (retainedCrossing_eq_of_firstOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp firstAxes.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp secondAxes.2
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp firstAxes.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp secondAxes.2
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp firstAxes.2
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp secondAxes.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp firstAxes.2
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp secondAxes.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have pointFstEqual :=
              retainedCrossing_point_fst_eq_of_secondOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointSndEqual :
                firstCrossing.point.2 =
                  secondCrossing.point.2 := by
              change
                20 * firstCrossing.point.2 + 1 =
                  20 * secondCrossing.point.2 + 1
                at coordinateEqual
              omega
            exact crossingDifferent
              (retainedCrossing_eq_of_secondOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · change
              20 * firstCrossing.point.2 + 1 =
                20 * secondCrossing.point.2 + 11
              at coordinateEqual
            omega
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp firstAxes.2
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp secondAxes.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp firstAxes.2
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp secondAxes.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · change
              20 * firstCrossing.point.2 + 11 =
                20 * secondCrossing.point.2 + 1
              at coordinateEqual
            omega
          · have pointFstEqual :=
              retainedCrossing_point_fst_eq_of_secondOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointSndEqual :
                firstCrossing.point.2 =
                  secondCrossing.point.2 := by
              change
                20 * firstCrossing.point.2 + 11 =
                  20 * secondCrossing.point.2 + 11
                at coordinateEqual
              omega
            exact crossingDifferent
              (retainedCrossing_eq_of_secondOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))

/-- A retained boundary lies strictly between the two terminals of its
supporting segment occurrence. -/
theorem retainedTerminal_boundary_orderCoordinate_extreme
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ retainedCrossingBoundaries graph)
    (keyEq : boundary.carrierKey = terminal.carrierKey)
    (axisAligned : terminal.indexed.segment.IsAxisAligned) :
    if terminal.IsLower then
      (CarrierNode.terminal terminal).orderCoordinate graph <
        (CarrierNode.boundary boundary).orderCoordinate graph
    else
      (CarrierNode.boundary boundary).orderCoordinate graph <
        (CarrierNode.terminal terminal).orderCoordinate graph := by
  have boundaryData :=
    retainedCrossingBoundary_indexed_mem_and_contains
      graph boundaryMem
  have terminalData :=
    drawingSegmentTerminal_indexed_mem graph terminalMem
  have carrierData :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (first := CarrierNode.boundary boundary)
      (second := CarrierNode.terminal terminal)
      boundaryData.1 terminalData.1
      (by simpa [CarrierNode.carrierKey] using keyEq)
  have pointData := boundaryData.2
  have crossingMem :=
    retainedCrossingBoundary_crossing_mem graph boundaryMem
  have crossingAxes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph crossingMem
  rcases axisAligned with horizontal | vertical
  · rw [carrierNode_terminal_orderCoordinate_horizontal
      graph terminal horizontal]
    rw [carrierNode_boundary_orderCoordinate]
    cases boundary with
    | mk crossing side =>
        cases side
        · simp only [CarrierNode.indexed, CarrierNode.translate,
            CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData
          simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne horizontal.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, horizontal.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CarrierNode.indexed, CarrierNode.translate,
            CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData
          simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne horizontal.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, horizontal.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CarrierNode.indexed,
            CrossingBoundary.indexed] at carrierData
          have crossingVertical :
              crossing.second.segment.IsVertical :=
            (GridSegment.isVertical_translate _ _).mp crossingAxes.2
          rw [carrierData.1] at crossingVertical
          exact (crossingVertical.2 horizontal.1).elim
        · simp only [CarrierNode.indexed,
            CrossingBoundary.indexed] at carrierData
          have crossingVertical :
              crossing.second.segment.IsVertical :=
            (GridSegment.isVertical_translate _ _).mp crossingAxes.2
          rw [carrierData.1] at crossingVertical
          exact (crossingVertical.2 horizontal.1).elim
  · rw [carrierNode_terminal_orderCoordinate_vertical
      graph terminal vertical]
    rw [carrierNode_boundary_orderCoordinate]
    cases boundary with
    | mk crossing side =>
        cases side
        · simp only [CarrierNode.indexed,
            CrossingBoundary.indexed] at carrierData
          have crossingHorizontal :
              crossing.first.segment.IsHorizontal :=
            (GridSegment.isHorizontal_translate _ _).mp crossingAxes.1
          rw [carrierData.1] at crossingHorizontal
          exact (vertical.2 crossingHorizontal.1).elim
        · simp only [CarrierNode.indexed,
            CrossingBoundary.indexed] at carrierData
          have crossingHorizontal :
              crossing.first.segment.IsHorizontal :=
            (GridSegment.isHorizontal_translate _ _).mp crossingAxes.1
          rw [carrierData.1] at crossingHorizontal
          exact (vertical.2 crossingHorizontal.1).elim
        · simp only [CarrierNode.indexed, CarrierNode.translate,
            CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData
          simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne vertical.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, vertical.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega
        · simp only [CarrierNode.indexed, CarrierNode.translate,
            CrossingBoundary.indexed,
            CrossingBoundary.translate] at carrierData
          simp only [CrossingBoundary.indexed,
            CrossingBoundary.translate] at pointData
          rw [carrierData.1, carrierData.2] at pointData
          simp [GridSegment.InteriorContains,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            GridSegment.StrictlyBetween, GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] at pointData
          generalize endpointEq : terminal.endpoint = endpoint
          cases endpoint <;>
            rcases lt_or_gt_of_ne vertical.2 with forward | backward <;>
            simp_all [SegmentTerminal.IsLower,
              SegmentTerminal.position, SegmentTerminal.drawingPoint,
              segmentTerminalLocalPosition, vertical.1,
              GridSegment.translate,
              PeriodicGridDrawing.periodTranslation,
              CrossingBoundary.position, crossingMacroOrigin,
              CrossingSide.localPosition, CrossoverVariable.position,
              planarMacroScale, Cell.add, Cell.scale] <;>
            (try split_ifs) <;> omega

/-- The horizontal and vertical occurrence keys of a retained proper
crossing are distinct. -/
theorem retainedCrossing_occurrenceKeys_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {record : CrossingRecord}
    (recordMem : record ∈ retainedCrossings graph) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        record.first record.firstTranslate ≠
      PeriodicGridDrawing.SegmentOccurrenceKey
        record.second record.secondTranslate := by
  have sound := retainedCrossings_sound graph recordMem
  have axes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph recordMem
  intro keyEqual
  have indexedEqual :
      record.first = record.second := by
    apply indexedSegment_eq_of_indices_eq
      (drawing graph) sound.1 sound.2.1
    · exact congrArg Prod.fst keyEqual
    · exact congrArg (fun key => key.2.1) keyEqual
  have firstHorizontal :
      record.first.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp axes.1
  have secondVertical :
      record.second.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp axes.2
  rw [indexedEqual] at firstHorizontal
  exact secondVertical.2 firstHorizontal.1

/-- Two retained carrier nodes on one occurrence with the same axial
coordinate are the same node. -/
theorem retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey)
    (coordinateEqual :
      first.orderCoordinate graph =
        second.orderCoordinate graph) :
    first = second := by
  cases first with
  | terminal firstTerminal =>
      have firstTerminalMem :
          firstTerminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at firstMem
        simpa using firstMem
      have firstAligned :
          firstTerminal.indexed.segment.IsAxisAligned :=
        drawing_isOrthogonal wellFormed isLocal degree
          firstTerminal.indexed
          (drawingSegmentTerminal_indexed_mem
            graph firstTerminalMem).1
      cases second with
      | terminal secondTerminal =>
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            unfold retainedDrawingCarrierNodes at secondMem
            simpa using secondMem
          by_contra different
          have extreme :=
            terminal_terminal_orderCoordinate_extreme
              graph firstTerminalMem secondTerminalMem
              keyEqual.symm (Ne.symm different) firstAligned
          by_cases lower : firstTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            unfold retainedDrawingCarrierNodes at secondMem
            simpa using secondMem
          have extreme :=
            retainedTerminal_boundary_orderCoordinate_extreme
              graph firstTerminalMem secondBoundaryMem
              keyEqual.symm firstAligned
          by_cases lower : firstTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
  | boundary firstBoundary =>
      have firstBoundaryMem :
          firstBoundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at firstMem
        simpa using firstMem
      cases second with
      | terminal secondTerminal =>
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            unfold retainedDrawingCarrierNodes at secondMem
            simpa using secondMem
          have secondAligned :
              secondTerminal.indexed.segment.IsAxisAligned :=
            drawing_isOrthogonal wellFormed isLocal degree
              secondTerminal.indexed
              (drawingSegmentTerminal_indexed_mem
                graph secondTerminalMem).1
          have extreme :=
            retainedTerminal_boundary_orderCoordinate_extreme
              graph secondTerminalMem firstBoundaryMem
              keyEqual secondAligned
          by_cases lower : secondTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            unfold retainedDrawingCarrierNodes at secondMem
            simpa using secondMem
          by_cases crossingEqual :
              firstBoundary.crossing = secondBoundary.crossing
          · rcases firstBoundary with
              ⟨crossing, firstSide⟩
            rcases secondBoundary with
              ⟨secondCrossing, secondSide⟩
            simp only at crossingEqual
            subst secondCrossing
            have crossingMem :=
              retainedCrossingBoundary_crossing_mem
                graph firstBoundaryMem
            have different :=
              retainedCrossing_occurrenceKeys_ne
                graph crossingMem
            cases firstSide <;> cases secondSide
            · rfl
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · exact (different keyEqual).elim
            · exact (different keyEqual).elim
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · rfl
            · exact (different keyEqual).elim
            · exact (different keyEqual).elim
            · exact (different keyEqual.symm).elim
            · exact (different keyEqual.symm).elim
            · rfl
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · exact (different keyEqual.symm).elim
            · exact (different keyEqual.symm).elim
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · rfl
          · exact False.elim
              ((retainedCrossingBoundary_orderCoordinate_ne_of_common_carrier
                wellFormed degree isLocal
                firstBoundaryMem secondBoundaryMem
                keyEqual crossingEqual) coordinateEqual)

/-- Every retained complete carrier chain is strictly sorted by its physical
axis coordinate. -/
theorem retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell) :
    (retainedCompleteCarrierNodes graph key).Pairwise
      fun first second =>
        first.orderCoordinate graph <
          second.orderCoordinate graph := by
  apply List.pairwise_lt_of_pairwise_le_of_nodup_of_injective
    (CarrierNode.orderCoordinate graph)
  · unfold retainedCompleteCarrierNodes
    exact List.pairwise_insertionSort _ _
  · exact retainedCompleteCarrierNodes_nodup graph key
  · intro first firstMem second secondMem coordinateEqual
    have firstData :=
      (mem_retainedCompleteCarrierNodes_iff
        graph key first).mp firstMem
    have secondData :=
      (mem_retainedCompleteCarrierNodes_iff
        graph key second).mp secondMem
    exact retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
      wellFormed degree isLocal
      firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)
      coordinateEqual

end PeriodicOrthocrossing
end LeanTrominoes

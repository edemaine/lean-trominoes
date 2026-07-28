import LeanTrominoes.PeriodicOrthocrossingCarrierCorrectionEndpoints

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

end PeriodicOrthocrossing
end LeanTrominoes

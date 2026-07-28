import LeanTrominoes.EmbeddedCNFIncidenceDrawingIndexedSegmentSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Separation at a common retained-drawing translate

Every final periodic segment occurrence has a representative segment in
the finite retained drawing and an anchor-adjusted physical shift.  When
two final occurrences have the same physical shift, finite planarity
separates their representatives unless their full periodic occurrence
keys agree.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Distinct final segment occurrences represented at the same translated
copy of the finite retained drawing have disjoint continuous interiors. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_samePhysicalShift_interiorsDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (firstWitness :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (secondWitness :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (samePhysicalShift :
      firstWitness.physicalShift =
        secondWitness.physicalShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have physicalKeyNe :
      firstWitness.physicalKey ≠ secondWitness.physicalKey := by
    intro physicalKeyEq
    exact different
      ((FinalGaugedSegmentOccurrenceWitness.physicalKey_eq_iff_segmentOccurrenceKey_eq
          firstWitness secondWitness).mp physicalKeyEq)
  have finiteDifferent :
      firstWitness.physicalIncidenceIndex ≠
          secondWitness.physicalIncidenceIndex ∨
        firstIndexed.segmentIndex ≠
          secondIndexed.segmentIndex := by
    by_cases incidenceIndexNe :
        firstWitness.physicalIncidenceIndex ≠
          secondWitness.physicalIncidenceIndex
    · exact Or.inl incidenceIndexNe
    · right
      intro segmentIndexEq
      apply physicalKeyNe
      apply Prod.ext
      · exact not_ne_iff.mp incidenceIndexNe
      · apply Prod.ext
        · exact segmentIndexEq
        · exact samePhysicalShift
  have rawPhysicalDisjoint :
      ¬GridSegment.InteriorsMeet
        firstWitness.physicalSegment
        secondWitness.physicalSegment :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.taggedSegments_interiorsDisjoint
        (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
        (retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
          formula wellFormed degree isLocal clausesNonempty)
        firstWitness.physicalIncidenceMember
        secondWitness.physicalIncidenceMember
        firstWitness.physicalSegmentMember
        secondWitness.physicalSegmentMember
        finiteDifferent
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have translatedPhysicalDisjoint :
      ¬GridSegment.InteriorsMeet
        (firstWitness.physicalSegment.translate
          (placement.translation firstWitness.physicalShift))
        (secondWitness.physicalSegment.translate
          (placement.translation secondWitness.physicalShift)) := by
    rw [samePhysicalShift]
    intro meet
    exact rawPhysicalDisjoint
      ((GridSegment.interiorsMeet_translate_both_iff
        firstWitness.physicalSegment
        secondWitness.physicalSegment
        (placement.translation secondWitness.physicalShift)).mp meet)
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq : drawing.gridSize = placement.period := by
    simpa [drawing, placement,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
      using
        PositionedPeriodicCNF.incidenceDrawing_gridSize
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          periodPositive
  have periodTranslationEq (shift : Cell) :
      drawing.periodTranslation shift =
        placement.translation shift := by
    simp only [PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation, gridSizeEq]
  have firstSegmentEq :
      firstIndexed.segment.translate
          (drawing.periodTranslation firstShift) =
        firstWitness.physicalSegment.translate
          (placement.translation firstWitness.physicalShift) := by
    rw [periodTranslationEq]
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.physicalShift,
      placement] using firstWitness.segmentEq
  have secondSegmentEq :
      secondIndexed.segment.translate
          (drawing.periodTranslation secondShift) =
        secondWitness.physicalSegment.translate
          (placement.translation secondWitness.physicalShift) := by
    rw [periodTranslationEq]
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.physicalShift,
      placement] using secondWitness.segmentEq
  simpa only [drawing, firstSegmentEq, secondSegmentEq] using
    translatedPhysicalDisjoint

end PeriodicOrthocrossing
end LeanTrominoes

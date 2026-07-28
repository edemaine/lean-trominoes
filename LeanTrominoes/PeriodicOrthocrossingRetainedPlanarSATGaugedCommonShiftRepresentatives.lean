import LeanTrominoes.EmbeddedCNFIncidenceDrawingIndexedSegmentSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences

/-!
# Common-shift retained representatives

Finite retained planarity applies whenever two final periodic segment
occurrences can be represented by genuine retained-drawing segments at one
common physical shift.  The original occurrence bridge supplies this
immediately when its two anchor-adjusted shifts agree.  Periodic component
orbit arguments will supply new retained representatives when they do not.

This file isolates the exact reusable transfer statement, so the remaining
orbit proof only needs to construct representatives and preserve their finite
incidence/segment distinction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A final periodic segment occurrence represented by one genuine segment
of the finite retained drawing at a prescribed common lattice shift. -/
structure FinalGaugedSegmentCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    (shift commonShift : Cell) where
  physicalIncidence :
    EmbeddedCNFIncidence (PlanarSATVariable Variable)
  physicalIncidenceIndex : Nat
  physicalIncidenceMember :
    (physicalIncidence, physicalIncidenceIndex) ∈
      (retainedDrawingPlanarSATLocalIncidenceDrawing
        formula).incidences.zipIdx
  physicalSegment : GridSegment
  physicalSegmentMember :
    (physicalSegment, indexed.segmentIndex) ∈
      (gridPolylineSegments
        ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          physicalIncidence)).zipIdx
  segmentEq :
    indexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift) =
      physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation commonShift)

/-- The segment equality stored by the original occurrence witness, with
the final drawing's period translation made explicit. -/
private theorem FinalGaugedSegmentOccurrenceWitness.segmentEq_finalDrawing
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    indexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift) =
      witness.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation witness.physicalShift) := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
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
  have periodTranslationEq :
      drawing.periodTranslation shift =
        placement.translation shift := by
    simp only [PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation, gridSizeEq]
  rw [periodTranslationEq]
  simpa only [drawing, placement,
    FinalGaugedSegmentOccurrenceWitness.physicalShift] using
    witness.segmentEq

/-- The original quotient-to-finite occurrence witness is a common-shift
representative at its anchor-adjusted physical shift. -/
def FinalGaugedSegmentOccurrenceWitness.toCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    FinalGaugedSegmentCommonShiftRepresentative
      formula indexed shift witness.physicalShift where
  physicalIncidence :=
    metadataPhysicalIncidence
      witness.routeWitness.metadata
      witness.routeWitness.metadataIndex
      witness.routeWitness.literal witness.taggedLiteral.2
  physicalIncidenceIndex := witness.physicalIncidenceIndex
  physicalIncidenceMember := witness.physicalIncidenceMember
  physicalSegment := witness.physicalSegment
  physicalSegmentMember := witness.physicalSegmentMember
  segmentEq := witness.segmentEq_finalDrawing

/-- Two distinct finite retained segments represented at one common shift
remain continuously disjoint in the final periodic lift. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_interiorsDisjoint
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
    {firstShift secondShift commonShift : Cell}
    (first :
      FinalGaugedSegmentCommonShiftRepresentative
        formula firstIndexed firstShift commonShift)
    (second :
      FinalGaugedSegmentCommonShiftRepresentative
        formula secondIndexed secondShift commonShift)
    (finiteDifferent :
      first.physicalIncidenceIndex ≠
          second.physicalIncidenceIndex ∨
        firstIndexed.segmentIndex ≠
          secondIndexed.segmentIndex) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have rawPhysicalDisjoint :
      ¬GridSegment.InteriorsMeet
        first.physicalSegment second.physicalSegment :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.taggedSegments_interiorsDisjoint
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
        formula wellFormed degree isLocal clausesNonempty)
      first.physicalIncidenceMember
      second.physicalIncidenceMember
      first.physicalSegmentMember
      second.physicalSegmentMember
      finiteDifferent
  intro meet
  rw [first.segmentEq, second.segmentEq] at meet
  exact rawPhysicalDisjoint
    ((GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment second.physicalSegment
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation commonShift)).mp meet)

end PeriodicOrthocrossing
end LeanTrominoes

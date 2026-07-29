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

/-- Translating both segments by one offset preserves the fact that the
first segment's interior avoids both endpoints of the second. -/
theorem endpointsAvoidInterior_translate_both
    (first second : GridSegment)
    (offset point : Cell)
    (rawAvoid :
      ∀ {rawPoint : Cell},
        first.InteriorContains rawPoint →
          rawPoint ≠ second.start ∧
            rawPoint ≠ second.finish)
    (firstContains :
      (first.translate offset).InteriorContains point) :
    point ≠ (second.translate offset).start ∧
      point ≠ (second.translate offset).finish := by
  let normalizedPoint := Cell.sub point offset
  have normalizedFirst :
      first.InteriorContains normalizedPoint := by
    apply
      (PeriodicGridDrawing.interiorContains_translate_iff
        first offset normalizedPoint).mp
    simpa [normalizedPoint, Cell.add, Cell.sub] using
      firstContains
  have normalizedAvoid := rawAvoid normalizedFirst
  constructor
  · intro pointEq
    apply normalizedAvoid.1
    have normalizedEq :=
      congrArg (fun endpoint => Cell.sub endpoint offset) pointEq
    simpa [normalizedPoint, GridSegment.translate,
      Cell.add, Cell.sub] using normalizedEq
  · intro pointEq
    apply normalizedAvoid.2
    have normalizedEq :=
      congrArg (fun endpoint => Cell.sub endpoint offset) pointEq
    simpa [normalizedPoint, GridSegment.translate,
      Cell.add, Cell.sub] using normalizedEq

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

/-- Two distinct finite retained segments represented at one common shift
also satisfy the asymmetric interior-versus-closed avoidance condition in
the final periodic lift. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_avoidsInterior
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
          secondIndexed.segmentIndex)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  have rawPhysicalAvoid :
      ∀ {rawPoint : Cell},
        first.physicalSegment.InteriorContains rawPoint →
          ¬second.physicalSegment.Contains rawPoint :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.taggedSegments_avoidsInterior
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
        formula wellFormed degree isLocal clausesNonempty)
      first.physicalIncidenceMember
      second.physicalIncidenceMember
      first.physicalSegmentMember
      second.physicalSegmentMember
      finiteDifferent
  intro secondContains
  rw [first.segmentEq] at firstContains
  rw [second.segmentEq] at secondContains
  let offset :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation commonShift
  let normalizedPoint := Cell.sub point offset
  have normalizedFirst :
      first.physicalSegment.InteriorContains normalizedPoint := by
    apply
      (PeriodicGridDrawing.interiorContains_translate_iff
        first.physicalSegment offset normalizedPoint).mp
    simpa [offset, normalizedPoint, Cell.add, Cell.sub] using
      firstContains
  have normalizedSecond :
      second.physicalSegment.Contains normalizedPoint := by
    apply
      (PeriodicGridDrawing.contains_translate_iff
        second.physicalSegment offset normalizedPoint).mp
    simpa [offset, normalizedPoint, Cell.add, Cell.sub] using
      secondContains
  exact rawPhysicalAvoid normalizedFirst normalizedSecond

/-- Two distinct retained segments represented at one common physical
shift preserve endpoint avoidance in the final periodic lift.  This is the
endpoint-sensitive companion to `commonShiftRepresentatives_avoidsInterior`
and remains informative for diagonal second segments. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_endpointsAvoidInterior
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
          secondIndexed.segmentIndex)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).start ∧
      point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).finish := by
  have rawPhysicalAvoid :
      ∀ {rawPoint : Cell},
        first.physicalSegment.InteriorContains rawPoint →
          rawPoint ≠ second.physicalSegment.start ∧
            rawPoint ≠ second.physicalSegment.finish :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.taggedSegments_endpointsAvoidInterior
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
        formula wellFormed degree isLocal clausesNonempty)
      first.physicalIncidenceMember
      second.physicalIncidenceMember
      first.physicalSegmentMember
      second.physicalSegmentMember
      finiteDifferent
  rw [first.segmentEq] at firstContains
  rw [second.segmentEq]
  exact
    endpointsAvoidInterior_translate_both
      first.physicalSegment second.physicalSegment
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation commonShift)
      point rawPhysicalAvoid firstContains

end PeriodicOrthocrossing
end LeanTrominoes

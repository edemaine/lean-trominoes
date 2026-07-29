import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedReindexingInjectivity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitNecessity

/-!
# Separation after physical component alignment

If translating the first physical source to the second occurrence's shift
identifies its component with the second retained source, the translated
source is automatically represented in the finite block.  Orbit necessity
then supplies the reindexing condition, and finite retained planarity
separates distinct periodic segment occurrences.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Component equality after the physical-shift difference is sufficient
for continuous separation of distinct final periodic segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_component_aligns_second
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (componentAlignment :
      second.routeWitness.metadata.source.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (Cell.sub first.physicalShift
            second.physicalShift)).component)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_retainedOrbitCondition
      formula wellFormed degree isLocal clausesNonempty
      first second
  · exact
      first.routeWitness.metadata.source
        |>.retainedOrbitCondition_of_retainedTarget
          formula first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          second.routeWitness.metadata.source
          second.source_retainedComponentMember
          componentAlignment
  · exact different

/-- Component equality after the physical-shift difference is also
sufficient for asymmetric interior-versus-closed avoidance of distinct
final periodic segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_component_aligns_second
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (componentAlignment :
      second.routeWitness.metadata.source.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (Cell.sub first.physicalShift
            second.physicalShift)).component)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  apply
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_retainedOrbitCondition
      formula wellFormed degree isLocal clausesNonempty
      first second
  · exact
      first.routeWitness.metadata.source
        |>.retainedOrbitCondition_of_retainedTarget
          formula first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          second.routeWitness.metadata.source
          second.source_retainedComponentMember
          componentAlignment
  · exact different
  · exact firstContains

/-- Component equality after the physical-shift difference is likewise
sufficient for endpoint separation of distinct final segment
occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_first_component_aligns_second
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (componentAlignment :
      second.routeWitness.metadata.source.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (Cell.sub first.physicalShift
            second.physicalShift)).component)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
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
  apply
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_first_retainedOrbitCondition
      formula wellFormed degree isLocal clausesNonempty
      first second
  · exact
      first.routeWitness.metadata.source
        |>.retainedOrbitCondition_of_retainedTarget
          formula first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          second.routeWitness.metadata.source
          second.source_retainedComponentMember
          componentAlignment
  · exact different
  · exact firstContains

end PeriodicOrthocrossing
end LeanTrominoes

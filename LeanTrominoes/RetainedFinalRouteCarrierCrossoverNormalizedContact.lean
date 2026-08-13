/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCarrierFrameTerminalContacts
import LeanTrominoes.PeriodicOrthocrossingCrossingNormalization
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverGeometry

/-!
# Normalized crossover contacts for arbitrary final carrier overlaps

In the crossover residue, first express the carrier in the direct source's
frame and then normalize the halo crossing to the canonical fundamental
square.  Applying the same normalization shift to the carrier makes its
supporting occurrence neighboring: it contains the normalized fundamental
crossing point.  The translated carrier is therefore a raw retained link,
and the existing finite crossover proximity theorem supplies exact endpoint
incidence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1600000

/-- Total carrier translation in the frame where a halo crossover has been
normalized to the fundamental square. -/
def FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord) : Cell :=
  Cell.add (carrier.relativeShiftTo macrocell)
    (Cell.neg (crossingPeriodShift formula.incidenceGraph crossing))

/-- The original selected carrier link in the normalized crossover frame. -/
def FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord) : EqualityLink CarrierNode :=
  carrierLinkPeriodTranslate formula.incidenceGraph carrier.link
    (carrier.normalizedCrossoverShift macrocell crossing)

/-- Carrier-frame overlap, translated into the direct frame, puts the
original direct macrocell center on the relatively translated carrier
support. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.relativeLink_supportingSegment_contains_center
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    ((carrier.relativeLinkTo macrocell).first.supportingSegment
        formula.incidenceGraph).Contains macrocell.center := by
  have baseContains :=
    carrier.supportingSegment_contains_relativeCenter
      wellFormed degree isLocal macrocell notSeparated
  have translatedContains :=
    (PeriodicGridDrawing.contains_translate_iff
      (carrier.link.first.supportingSegment formula.incidenceGraph)
      ((drawing formula.incidenceGraph).periodTranslation
        (carrier.relativeShiftTo macrocell))
      (macrocell.relativeCenterFrom carrier)).mpr baseContains
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases carrierShiftEq : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftEq : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  have pointCancel :
      Cell.add (macrocell.relativeCenterFrom carrier)
          ((drawing formula.incidenceGraph).periodTranslation
            (carrier.relativeShiftTo macrocell)) =
        macrocell.center := by
    apply Prod.ext <;>
      simp [FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
        FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom,
        FinalGaugedRouteMacrocellOccurrenceWitness.relativeShiftFrom,
        PeriodicGridDrawing.periodTranslation,
        centerEq, carrierShiftEq, macrocellShiftEq,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  rw [pointCancel] at translatedContains
  simpa [FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo,
    FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
    CarrierNode.supportingSegment_periodTranslate, centerEq] using
      translatedContains

/-- In the normalized crossover frame, the translated carrier support
contains the canonical crossing point. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink_supportingSegment_contains
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (centerEq : macrocell.center = crossing.point)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    ((carrier.normalizedCrossoverLink macrocell crossing).first
        |>.supportingSegment formula.incidenceGraph).Contains
      (crossing.periodNormalize formula.incidenceGraph).point := by
  have directContains :=
    carrier.relativeLink_supportingSegment_contains_center
      wellFormed degree isLocal macrocell notSeparated
  have translatedContains :=
    (PeriodicGridDrawing.contains_translate_iff
      ((carrier.relativeLinkTo macrocell).first
        |>.supportingSegment formula.incidenceGraph)
      ((drawing formula.incidenceGraph).periodTranslation
        (Cell.neg
          (crossingPeriodShift formula.incidenceGraph crossing)))
      macrocell.center).mpr directContains
  rcases centerValue : macrocell.center with ⟨centerX, centerY⟩
  rcases crossingPointValue : crossing.point with
    ⟨crossingX, crossingY⟩
  rcases periodShiftValue :
      crossingPeriodShift formula.incidenceGraph crossing with
    ⟨periodShiftX, periodShiftY⟩
  rcases carrierShiftValue : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftValue : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  have pointCoordinates : centerX = crossingX ∧ centerY = crossingY := by
    simpa [centerValue, crossingPointValue] using centerEq
  have normalizedPointEq :
      Cell.add macrocell.center
          ((drawing formula.incidenceGraph).periodTranslation
            (Cell.neg
              (crossingPeriodShift formula.incidenceGraph crossing))) =
        (crossing.periodNormalize formula.incidenceGraph).point := by
    apply Prod.ext <;>
      simp [CrossingRecord.periodNormalize,
        PeriodicGridDrawing.normalizePoint,
        PeriodicGridDrawing.periodTranslation,
        centerValue, crossingPointValue, periodShiftValue,
        pointCoordinates.1, pointCoordinates.2,
        Cell.add, Cell.sub, Cell.neg, Cell.scale] <;>
      ring
  have normalizedSegmentEq :
      (((carrier.relativeLinkTo macrocell).first
          |>.supportingSegment formula.incidenceGraph).translate
        ((drawing formula.incidenceGraph).periodTranslation
          (Cell.neg
            (crossingPeriodShift formula.incidenceGraph crossing)))) =
        ((carrier.normalizedCrossoverLink macrocell crossing).first
          |>.supportingSegment formula.incidenceGraph) := by
    rcases supportValue :
        carrier.link.first.supportingSegment formula.incidenceGraph with
      ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
    simp only [
      FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink,
      FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverShift,
      FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo,
      FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
      carrierLinkPeriodTranslate_first,
      CarrierNode.supportingSegment_periodTranslate]
    simp [supportValue, GridSegment.translate,
      PeriodicGridDrawing.periodTranslation,
      periodShiftValue, carrierShiftValue, macrocellShiftValue,
      Cell.add, Cell.sub, Cell.neg, Cell.scale]
    constructor <;> constructor <;> ring
  rw [normalizedPointEq, normalizedSegmentEq] at translatedContains
  exact translatedContains

/-- The normalized carrier occurrence is neighboring because its support
contains the normalized crossing point in the fundamental square. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink_first_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (centerEq : macrocell.center = crossing.point)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    IsNeighborTranslation
      (carrier.normalizedCrossoverLink macrocell crossing).first.translate := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      formula.incidenceGraph carrier.link_mem
  have indexedMember :=
    retainedCarrierNode_indexed_mem formula.incidenceGraph endpoints.1
  apply drawing_occurrence_translate_isNeighbor_of_contains
    wellFormed degree isLocal indexedMember
    (periodNormalize_point_inFundamental
      formula.incidenceGraph crossing)
  simpa [FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink,
    CarrierNode.supportingSegment] using
      carrier.normalizedCrossoverLink_supportingSegment_contains
        wellFormed degree isLocal macrocell crossing
        centerEq notSeparated

/-- The normalized carrier link belongs to the raw retained link family. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink_mem_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (centerEq : macrocell.center = crossing.point)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    carrier.normalizedCrossoverLink macrocell crossing ∈
      retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
  unfold FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink
  apply retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph carrier.link).mp carrier.link_mem).1
    (carrier.normalizedCrossoverShift macrocell crossing)
    carrier.link_first_neighbor
  exact
    carrier.normalizedCrossoverLink_first_neighbor
      wellFormed degree isLocal macrocell crossing
      centerEq notSeparated

/-- Normalizing a retained halo crossover produces another enumerated halo
crossing, now with a fundamental-square point. -/
theorem crossing_periodNormalize_mem_orientedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {crossing : CrossingRecord}
    (crossingMember : crossing ∈ orientedCrossingHalo graph) :
    crossing.periodNormalize graph ∈ orientedCrossingHalo graph :=
  orientedCrossings_subset_orientedCrossingHalo graph
    (periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal crossingMember)

/-- Rectangle overlap is preserved when the direct-frame carrier and halo
crossing are translated together into the normalized crossover frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (centerEq : macrocell.center = crossing.point)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph
          (carrier.normalizedCrossoverLink macrocell crossing))
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrier.normalizedCrossoverLink macrocell crossing))
        (planarSATMacrocellRouteLower
          (crossing.periodNormalize formula.incidenceGraph).point)
        (planarSATMacrocellRouteUpper
          (crossing.periodNormalize formula.incidenceGraph).point) := by
  have relativeOverlap :=
    carrier.relativeLink_macrocell_overlap macrocell notSeparated
  rw [centerEq] at relativeOverlap
  let crossingShift :=
    crossingPeriodShift formula.incidenceGraph crossing
  let offset :=
    carrierMacroPeriodTranslation formula.incidenceGraph crossingShift
  have linkLowerEq :
      Cell.add offset
          (drawingCompleteCarrierLinkRectangleLower
            formula.incidenceGraph
            (carrier.normalizedCrossoverLink macrocell crossing)) =
        drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph (carrier.relativeLinkTo macrocell) := by
    rcases carrierShiftValue : carrier.physicalShift with
      ⟨carrierShiftX, carrierShiftY⟩
    rcases macrocellShiftValue : macrocell.physicalShift with
      ⟨macrocellShiftX, macrocellShiftY⟩
    rcases crossingShiftValue : crossingShift with
      ⟨crossingShiftX, crossingShiftY⟩
    apply Prod.ext <;>
      simp [offset,
        FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink,
        FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverShift,
        FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo,
        FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
        drawingCompleteCarrierLinkRectangleLower_periodTranslate,
        carrierMacroPeriodTranslation,
        carrierShiftValue, macrocellShiftValue,
        crossingShiftValue, crossingShift,
        Cell.add, Cell.sub, Cell.neg, Cell.scale] <;>
      ring
  have linkUpperEq :
      Cell.add offset
          (drawingCompleteCarrierLinkRectangleUpper
            formula.incidenceGraph
            (carrier.normalizedCrossoverLink macrocell crossing)) =
        drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph (carrier.relativeLinkTo macrocell) := by
    rcases carrierShiftValue : carrier.physicalShift with
      ⟨carrierShiftX, carrierShiftY⟩
    rcases macrocellShiftValue : macrocell.physicalShift with
      ⟨macrocellShiftX, macrocellShiftY⟩
    rcases crossingShiftValue : crossingShift with
      ⟨crossingShiftX, crossingShiftY⟩
    apply Prod.ext <;>
      simp [offset,
        FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverLink,
        FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverShift,
        FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo,
        FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
        drawingCompleteCarrierLinkRectangleUpper_periodTranslate,
        carrierMacroPeriodTranslation,
        carrierShiftValue, macrocellShiftValue,
        crossingShiftValue, crossingShift,
        Cell.add, Cell.sub, Cell.neg, Cell.scale] <;>
      ring
  have crossingLowerEq :
      Cell.add offset
          (planarSATMacrocellRouteLower
            (crossing.periodNormalize formula.incidenceGraph).point) =
        planarSATMacrocellRouteLower crossing.point := by
    rcases crossingPointValue : crossing.point with
      ⟨crossingX, crossingY⟩
    rcases crossingShiftValue : crossingShift with
      ⟨crossingShiftX, crossingShiftY⟩
    apply Prod.ext <;>
      simp [offset, crossingShift,
        CrossingRecord.periodNormalize,
        PeriodicGridDrawing.normalizePoint,
        PeriodicGridDrawing.periodTranslation,
        planarSATMacrocellRouteLower,
        carrierMacroPeriodTranslation,
        crossingPointValue, crossingShiftValue,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  have crossingUpperEq :
      Cell.add offset
          (planarSATMacrocellRouteUpper
            (crossing.periodNormalize formula.incidenceGraph).point) =
        planarSATMacrocellRouteUpper crossing.point := by
    rcases crossingPointValue : crossing.point with
      ⟨crossingX, crossingY⟩
    rcases crossingShiftValue : crossingShift with
      ⟨crossingShiftX, crossingShiftY⟩
    apply Prod.ext <;>
      simp [offset, crossingShift,
        CrossingRecord.periodNormalize,
        PeriodicGridDrawing.normalizePoint,
        PeriodicGridDrawing.periodTranslation,
        planarSATMacrocellRouteUpper,
        carrierMacroPeriodTranslation,
        crossingPointValue, crossingShiftValue,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  intro normalizedSeparated
  have translatedSeparated :=
    (ClosedGridRectanglesSeparated.add_iff
      (drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph
        (carrier.normalizedCrossoverLink macrocell crossing))
      (drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph
        (carrier.normalizedCrossoverLink macrocell crossing))
      (planarSATMacrocellRouteLower
        (crossing.periodNormalize formula.incidenceGraph).point)
      (planarSATMacrocellRouteUpper
        (crossing.periodNormalize formula.incidenceGraph).point)
      offset).mpr normalizedSeparated
  rw [linkLowerEq, linkUpperEq,
    crossingLowerEq, crossingUpperEq] at translatedSeparated
  exact relativeOverlap translatedSeparated

/-- A final carrier overlap with a crossover source yields exact incidence
after canonical normalization of the common finite frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      macrocell.metadata.source =
        .crossover crossing localClauseIndex)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    CarrierLinkIncidentToCrossover
      (carrier.normalizedCrossoverLink macrocell crossing)
      (crossing.periodNormalize formula.incidenceGraph) := by
  have crossingMember :
      crossing ∈ orientedCrossingHalo formula.incidenceGraph := by
    have sourceMember :=
      (macrocell.metadata
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mp macrocell.metadata_retainedValid |>.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  have centerEq : macrocell.center = crossing.point := by
    have advertised := macrocell.centerEq
    rw [sourceEq] at advertised
    simpa [DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.macrocellCenter] using
        Option.some.inj advertised.symm
  exact
    retainedDrawingCompleteCarrierLinkRaw_incidentToCrossover_of_overlap
      wellFormed degree isLocal
      (carrier.normalizedCrossoverLink_mem_raw
        wellFormed degree isLocal macrocell crossing
        centerEq notSeparated)
      (crossing_periodNormalize_mem_orientedCrossingHalo
        wellFormed degree isLocal crossingMember)
      (carrier.normalizedCrossoverLink_overlap
        macrocell crossing centerEq notSeparated)

end PeriodicOrthocrossing
end LeanTrominoes

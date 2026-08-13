/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCarrierMacrocellOverlapNormalization
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierMacrocellSeparation

/-!
# Normalizing final overlaps in the selected carrier frame

The noncarrier-frame normalization translates the carrier link by the
difference of the two recovered physical shifts.  That translated link need
not itself be one of the finite retained representatives.  For the contact
argument it is more useful to keep the carrier's original selected link fixed
and translate the noncarrier macrocell by the opposite relative shift.

This file proves the corresponding common-frame rectangle identity.  It also
extracts selected-link membership from the carrier occurrence and turns an
overlap into containment of the relative macrocell center in the carrier's
supporting segment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Period shift moving an arbitrary noncarrier occurrence into the original
selected carrier link's physical frame. -/
def FinalGaugedRouteMacrocellOccurrenceWitness.relativeShiftFrom
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift) :
    Cell :=
  Cell.sub macrocell.physicalShift carrier.physicalShift

/-- The noncarrier macrocell center expressed in the original selected
carrier link's physical frame. -/
def FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift) :
    Cell :=
  Cell.add macrocell.center
    ((drawing formula.incidenceGraph).periodTranslation
      (macrocell.relativeShiftFrom carrier))

/-- The final macrocell lower corner is its carrier-frame lower corner
translated by the carrier occurrence's physical offset. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.macrocellLower_eq_add_carrierFrame
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift) :
    planarSATMacrocellRouteLower macrocell.translatedCenter =
      Cell.add carrier.physicalOffset
        (planarSATMacrocellRouteLower
          (macrocell.relativeCenterFrom carrier)) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases macrocellShiftEq : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  rcases carrierShiftEq : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom,
      FinalGaugedRouteMacrocellOccurrenceWitness.relativeShiftFrom,
      FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      planarSATMacrocellRouteLower,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, macrocellShiftEq, carrierShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The final macrocell upper corner is its carrier-frame upper corner
translated by the carrier occurrence's physical offset. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.macrocellUpper_eq_add_carrierFrame
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift) :
    planarSATMacrocellRouteUpper macrocell.translatedCenter =
      Cell.add carrier.physicalOffset
        (planarSATMacrocellRouteUpper
          (macrocell.relativeCenterFrom carrier)) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases macrocellShiftEq : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  rcases carrierShiftEq : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom,
      FinalGaugedRouteMacrocellOccurrenceWitness.relativeShiftFrom,
      FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      planarSATMacrocellRouteUpper,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, macrocellShiftEq, carrierShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Arbitrary final carrier--macrocell rectangle separation is exactly
separation between the original selected carrier link and the relative
macrocell center in the carrier's physical frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.rectanglesSeparated_iff_carrierFrame
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
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift) :
    ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter) ↔
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph carrier.link)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph carrier.link)
        (planarSATMacrocellRouteLower
          (macrocell.relativeCenterFrom carrier))
        (planarSATMacrocellRouteUpper
          (macrocell.relativeCenterFrom carrier)) := by
  rw [show carrier.rectangleLower =
        Cell.add carrier.physicalOffset
          (drawingCompleteCarrierLinkRectangleLower
            formula.incidenceGraph carrier.link) by rfl,
    show carrier.rectangleUpper =
        Cell.add carrier.physicalOffset
          (drawingCompleteCarrierLinkRectangleUpper
            formula.incidenceGraph carrier.link) by rfl,
    macrocell.macrocellLower_eq_add_carrierFrame carrier,
    macrocell.macrocellUpper_eq_add_carrierFrame carrier]
  exact
    ClosedGridRectanglesSeparated.add_iff
      (drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph carrier.link)
      (drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph carrier.link)
      (planarSATMacrocellRouteLower
        (macrocell.relativeCenterFrom carrier))
      (planarSATMacrocellRouteUpper
        (macrocell.relativeCenterFrom carrier))
      carrier.physicalOffset

/-- Failure of final rectangle separation gives overlap in the selected
carrier link's physical frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.link_relativeMacrocell_overlap
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
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph carrier.link)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph carrier.link)
        (planarSATMacrocellRouteLower
          (macrocell.relativeCenterFrom carrier))
        (planarSATMacrocellRouteUpper
          (macrocell.relativeCenterFrom carrier)) := by
  exact fun separated =>
    notSeparated
      ((carrier.rectanglesSeparated_iff_carrierFrame macrocell).mpr
        separated)

/-- The link stored by a carrier occurrence is an actual selected retained
carrier representative, independently of the occurrence's external shift. -/
theorem FinalGaugedCarrierRouteOccurrenceWitness.link_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    carrier.link ∈
      retainedDrawingCompleteCarrierLinks formula.incidenceGraph := by
  rcases
      carrier.metadata.source.exists_eq_carrier_of_component_eq
        carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceMember :=
    (carrier.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp carrier.metadata_retainedValid |>.1
  rw [sourceEq] at sourceMember
  simpa only [DrawingPlanarSATClauseSource.RetainedComponentMember] using
    sourceMember

/-- The first occurrence of a carrier occurrence's selected link is in the
nine-neighbor window. -/
theorem FinalGaugedCarrierRouteOccurrenceWitness.link_first_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    IsNeighborTranslation carrier.link.first.translate :=
  retainedDrawingCompleteCarrierLink_first_translate_neighbor
    formula.incidenceGraph carrier.link_mem

/-- An overlap forces the relative macrocell center onto the supporting
segment of the original selected carrier representative. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.supportingSegment_contains_relativeCenter
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
    (carrier.link.first.supportingSegment formula.incidenceGraph).Contains
      (macrocell.relativeCenterFrom carrier) := by
  exact
    retainedDrawingCompleteCarrierLink_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal carrier.link_mem
      (macrocell.relativeCenterFrom carrier)
      (carrier.link_relativeMacrocell_overlap macrocell notSeparated)

end PeriodicOrthocrossing
end LeanTrominoes

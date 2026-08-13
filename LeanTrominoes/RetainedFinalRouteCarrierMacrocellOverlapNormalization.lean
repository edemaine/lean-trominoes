/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCarrierBounds
import LeanTrominoes.RetainedFinalFlatCarrierMacrocellOverlapNormalization

/-!
# Normalizing arbitrary final carrier--macrocell overlaps

The flat overlap normalization applies at external shift zero.  Copied-source
separation compares occurrences at unrelated quotient shifts, but the same
common-frame calculation depends only on their recovered physical shifts.

This file expresses an arbitrary carrier occurrence in the physical frame of
an arbitrary noncarrier occurrence.  Translating both enclosing rectangles
back by the noncarrier offset turns the final overlap test into the finite
test between a relative carrier link and the original macrocell center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Period shift moving an arbitrary carrier occurrence into the physical
frame of an arbitrary noncarrier occurrence. -/
def FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo
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
    Cell :=
  Cell.sub carrier.physicalShift macrocell.physicalShift

/-- The arbitrary carrier link expressed in the noncarrier occurrence's
physical frame. -/
def FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo
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
    EqualityLink CarrierNode :=
  carrierLinkPeriodTranslate formula.incidenceGraph carrier.link
    (carrier.relativeShiftTo macrocell)

/-- Physical planar-SAT offset of an arbitrary noncarrier occurrence. -/
def FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  carrierMacroPeriodTranslation formula.incidenceGraph
    macrocell.physicalShift

/-- The final carrier lower corner is the relative carrier lower corner
translated by the reference occurrence's physical offset. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.rectangleLower_eq_add_relativeLink
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
    carrier.rectangleLower =
      Cell.add macrocell.physicalOffset
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell)) := by
  unfold FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo
  rw [drawingCompleteCarrierLinkRectangleLower_periodTranslate]
  rcases carrierShiftEq : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftEq : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedCarrierRouteOccurrenceWitness.rectangleLower,
      FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset,
      FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
      FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      carrierMacroPeriodTranslation,
      carrierShiftEq, macrocellShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The final carrier upper corner is the relative carrier upper corner
translated by the reference occurrence's physical offset. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.rectangleUpper_eq_add_relativeLink
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
    carrier.rectangleUpper =
      Cell.add macrocell.physicalOffset
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell)) := by
  unfold FinalGaugedCarrierRouteOccurrenceWitness.relativeLinkTo
  rw [drawingCompleteCarrierLinkRectangleUpper_periodTranslate]
  rcases carrierShiftEq : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftEq : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedCarrierRouteOccurrenceWitness.rectangleUpper,
      FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset,
      FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
      FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      carrierMacroPeriodTranslation,
      carrierShiftEq, macrocellShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The final macrocell lower corner is its finite-frame lower corner
translated by the occurrence's physical offset. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.macrocellLower_eq_add
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    planarSATMacrocellRouteLower macrocell.translatedCenter =
      Cell.add macrocell.physicalOffset
        (planarSATMacrocellRouteLower macrocell.center) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases shiftEq : macrocell.physicalShift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset,
      planarSATMacrocellRouteLower,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, shiftEq, Cell.add, Cell.scale] <;>
    ring

/-- The final macrocell upper corner is its finite-frame upper corner
translated by the occurrence's physical offset. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.macrocellUpper_eq_add
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    planarSATMacrocellRouteUpper macrocell.translatedCenter =
      Cell.add macrocell.physicalOffset
        (planarSATMacrocellRouteUpper macrocell.center) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases shiftEq : macrocell.physicalShift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset,
      planarSATMacrocellRouteUpper,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, shiftEq, Cell.add, Cell.scale] <;>
    ring

/-- Arbitrary final carrier--macrocell rectangle separation is exactly
separation in the noncarrier occurrence's physical frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.rectanglesSeparated_iff_relativeLink
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
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell))
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell))
        (planarSATMacrocellRouteLower macrocell.center)
        (planarSATMacrocellRouteUpper macrocell.center) := by
  rw [carrier.rectangleLower_eq_add_relativeLink macrocell,
    carrier.rectangleUpper_eq_add_relativeLink macrocell,
    macrocell.macrocellLower_eq_add,
    macrocell.macrocellUpper_eq_add]
  exact
    ClosedGridRectanglesSeparated.add_iff
      (drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph
        (carrier.relativeLinkTo macrocell))
      (drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph
        (carrier.relativeLinkTo macrocell))
      (planarSATMacrocellRouteLower macrocell.center)
      (planarSATMacrocellRouteUpper macrocell.center)
      macrocell.physicalOffset

/-- Failure of the translated separation test gives the relative finite-frame
overlap hypothesis. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.relativeLink_macrocell_overlap
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
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell))
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell))
        (planarSATMacrocellRouteLower macrocell.center)
        (planarSATMacrocellRouteUpper macrocell.center) := by
  exact fun separated =>
    notSeparated
      ((carrier.rectanglesSeparated_iff_relativeLink macrocell).mpr
        separated)

end PeriodicOrthocrossing
end LeanTrominoes

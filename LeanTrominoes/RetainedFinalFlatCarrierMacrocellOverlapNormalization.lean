import LeanTrominoes.RetainedFinalFlatRouteComponentCases
import LeanTrominoes.PeriodicOrthocrossingRetainedTranslatedCarrierGeometry

/-!
# Normalizing a flat carrier--macrocell overlap

The last carrier/noncarrier fan case is initially stated in final quotient
coordinates: both finite components have been translated by their recovered
physical shifts.  Translating the whole picture back by the noncarrier
occurrence's shift puts its macrocell at the original finite center and moves
the carrier link by the difference of the two physical shifts.

This file records that common-frame normalization.  In particular, failure
of the final translated rectangle-separation test is exactly failure of the
corresponding test between the relative carrier link and the unshifted
noncarrier macrocell.
-/

namespace LeanTrominoes

/-- Translating all four corners by the same offset preserves and reflects
strict separation of two closed grid rectangles. -/
theorem ClosedGridRectanglesSeparated.add_iff
    (firstLower firstUpper secondLower secondUpper offset : Cell) :
    ClosedGridRectanglesSeparated
        (Cell.add offset firstLower)
        (Cell.add offset firstUpper)
        (Cell.add offset secondLower)
        (Cell.add offset secondUpper) ↔
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [ClosedGridRectanglesSeparated, Cell.add]
  omega

namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Period shift moving a flat carrier occurrence into the physical frame
of a flat noncarrier occurrence. -/
def FinalGaugedFlatCarrierRouteWitness.relativeShiftTo
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute) :
    Cell :=
  Cell.sub carrier.routeWitness.physicalShift
    macrocell.routeWitness.physicalShift

/-- The carrier link expressed in the noncarrier occurrence's physical
frame. -/
def FinalGaugedFlatCarrierRouteWitness.relativeLinkTo
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute) :
    EqualityLink CarrierNode :=
  carrierLinkPeriodTranslate formula.incidenceGraph carrier.link
    (carrier.relativeShiftTo macrocell)

/-- Physical planar-SAT offset of the reference noncarrier occurrence. -/
def FinalGaugedFlatRouteMacrocellWitness.physicalOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) :
    Cell :=
  carrierMacroPeriodTranslation formula.incidenceGraph
    macrocell.routeWitness.physicalShift

/-- The final carrier lower corner is the relative carrier lower corner
translated by the reference occurrence's physical offset. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.rectangleLower_eq_add_relativeLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute) :
    carrier.rectangleLower =
      Cell.add macrocell.physicalOffset
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell)) := by
  unfold FinalGaugedFlatCarrierRouteWitness.relativeLinkTo
  rw [drawingCompleteCarrierLinkRectangleLower_periodTranslate]
  rcases carrierShiftEq : carrier.routeWitness.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftEq : macrocell.routeWitness.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedFlatCarrierRouteWitness.rectangleLower,
      FinalGaugedFlatCarrierRouteWitness.physicalOffset,
      FinalGaugedFlatCarrierRouteWitness.relativeShiftTo,
      FinalGaugedFlatRouteMacrocellWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      carrierMacroPeriodTranslation,
      carrierShiftEq, macrocellShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The final carrier upper corner is the relative carrier upper corner
translated by the reference occurrence's physical offset. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.rectangleUpper_eq_add_relativeLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute) :
    carrier.rectangleUpper =
      Cell.add macrocell.physicalOffset
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrier.relativeLinkTo macrocell)) := by
  unfold FinalGaugedFlatCarrierRouteWitness.relativeLinkTo
  rw [drawingCompleteCarrierLinkRectangleUpper_periodTranslate]
  rcases carrierShiftEq : carrier.routeWitness.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftEq : macrocell.routeWitness.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedFlatCarrierRouteWitness.rectangleUpper,
      FinalGaugedFlatCarrierRouteWitness.physicalOffset,
      FinalGaugedFlatCarrierRouteWitness.relativeShiftTo,
      FinalGaugedFlatRouteMacrocellWitness.physicalOffset,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      carrierMacroPeriodTranslation,
      carrierShiftEq, macrocellShiftEq,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The final macrocell lower corner is its finite-frame lower corner
translated by the occurrence's physical offset. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.macrocellLower_eq_add
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) :
    planarSATMacrocellRouteLower macrocell.translatedCenter =
      Cell.add macrocell.physicalOffset
        (planarSATMacrocellRouteLower macrocell.center) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases shiftEq : macrocell.routeWitness.physicalShift with
    ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedFlatRouteMacrocellWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedFlatRouteMacrocellWitness.physicalOffset,
      planarSATMacrocellRouteLower,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, shiftEq, Cell.add, Cell.scale] <;>
    ring

/-- The final macrocell upper corner is its finite-frame upper corner
translated by the occurrence's physical offset. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.macrocellUpper_eq_add
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) :
    planarSATMacrocellRouteUpper macrocell.translatedCenter =
      Cell.add macrocell.physicalOffset
        (planarSATMacrocellRouteUpper macrocell.center) := by
  rcases centerEq : macrocell.center with ⟨centerX, centerY⟩
  rcases shiftEq : macrocell.routeWitness.physicalShift with
    ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedFlatRouteMacrocellWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      FinalGaugedFlatRouteMacrocellWitness.physicalOffset,
      planarSATMacrocellRouteUpper,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      centerEq, shiftEq, Cell.add, Cell.scale] <;>
    ring

/-- Final carrier--macrocell rectangle separation is exactly separation in
the noncarrier occurrence's physical frame. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.rectanglesSeparated_iff_relativeLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute) :
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

/-- Failure of the final translated separation test therefore gives the
unnormalized overlap hypothesis expected by the finite carrier proximity
API. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.relativeLink_macrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
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

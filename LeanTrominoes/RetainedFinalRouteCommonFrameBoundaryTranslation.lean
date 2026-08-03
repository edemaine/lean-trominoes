import LeanTrominoes.RetainedFinalRouteCommonFrameOffsets
import LeanTrominoes.RetainedFinalFlatNormalizedBoundary

/-!
# Translating carrier boundaries out of a common frame

A carrier boundary is covariant under a common translation of its two route
lists and its macrocell origin.  This file packages the inverse direction
needed after constructing a boundary in a finite contact frame.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Remove a common translation from both routes of a carrier-boundary
certificate, translating its origin back by the same offset. -/
def FinalGaugedFlatNormalizedCarrierBoundary.of_commonTranslation
    {carrierRoute macrocellRoute : List Cell}
    (offset : Cell)
    (boundary :
      FinalGaugedFlatNormalizedCarrierBoundary
        (translatePolyline offset carrierRoute)
        (translatePolyline offset macrocellRoute)) :
    FinalGaugedFlatNormalizedCarrierBoundary
      carrierRoute macrocellRoute where
  port := boundary.port
  origin := Cell.sub boundary.origin offset
  carrierOutside point pointMember := by
    have translatedMember :
        Cell.add offset point ∈
          translatePolyline offset carrierRoute := by
      exact List.mem_map.mpr ⟨point, pointMember, rfl⟩
    have outside :=
      boundary.carrierOutside
        (Cell.add offset point) translatedMember
    have subEq :
        Cell.sub point (Cell.sub boundary.origin offset) =
          Cell.sub (Cell.add offset point) boundary.origin := by
      apply Prod.ext <;> simp [Cell.add, Cell.sub] <;> ring
    change
      boundary.port.OutsideCarrierBoundary
        (Cell.sub point (Cell.sub boundary.origin offset))
    rw [subEq]
    exact outside
  macrocellInside point pointMember := by
    have translatedMember :
        Cell.add offset point ∈
          translatePolyline offset macrocellRoute := by
      exact List.mem_map.mpr ⟨point, pointMember, rfl⟩
    have inside :=
      boundary.macrocellInside
        (Cell.add offset point) translatedMember
    have subEq :
        Cell.sub point (Cell.sub boundary.origin offset) =
          Cell.sub (Cell.add offset point) boundary.origin := by
      apply Prod.ext <;> simp [Cell.add, Cell.sub] <;> ring
    change
      boundary.port.InsideCarrierBoundary
        (Cell.sub point (Cell.sub boundary.origin offset))
    rw [subEq]
    exact inside

/-- Translate a boundary for two independently reindexed route occurrences
back to their original final frame once their physical offsets agree. -/
def FinalGaugedFlatNormalizedCarrierBoundary.of_commonFrame
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
    (carrierReindexShift macrocellReindexShift : Cell)
    (offsetEq :
      carrier.commonFrameOffset carrierReindexShift =
        macrocell.commonFrameOffset macrocellReindexShift)
    (boundary :
      FinalGaugedFlatNormalizedCarrierBoundary
        (carrier.commonFrameRoute carrierReindexShift)
        (macrocell.commonFrameRoute macrocellReindexShift)) :
    FinalGaugedFlatNormalizedCarrierBoundary
      (finalGaugedRouteOccurrence formula
        carrierClauseIndex carrierLiteralIndex carrierShift)
      (finalGaugedRouteOccurrence formula
        macrocellClauseIndex macrocellLiteralIndex macrocellShift) := by
  have translatedBoundary :
      FinalGaugedFlatNormalizedCarrierBoundary
        (translatePolyline
          (carrier.commonFrameOffset carrierReindexShift)
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift))
        (translatePolyline
          (carrier.commonFrameOffset carrierReindexShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex macrocellShift)) := by
    simpa only [FinalGaugedRouteOccurrenceWitness.commonFrameRoute,
      offsetEq] using boundary
  exact
    FinalGaugedFlatNormalizedCarrierBoundary.of_commonTranslation
      (carrier.commonFrameOffset carrierReindexShift)
      translatedBoundary

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.RetainedFinalRouteContactCommonFrameSources

/-!
# Common physical offsets for arbitrary carrier contacts

The carrier and direct route are reindexed by different drawing-period
shifts at a terminal or normalized crossover contact.  Their compensating
macro-period translations are nevertheless identical.  Thus both selected
finite routes live in one genuinely common physical frame.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Zero acts trivially on complete physical carrier links. -/
@[simp]
theorem carrierLinkPeriodTranslate_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) :
    carrierLinkPeriodTranslate graph link (0, 0) = link := by
  rcases link with ⟨first, second, ⟨forward, backward⟩⟩
  simp [carrierLinkPeriodTranslate,
    EqualityPositions.periodTranslate,
    carrierMacroPeriodTranslation, Cell.scale]

/-- Keeping the selected carrier link fixed and translating the macrocell by
its relative shift applies the same physical offset to both final routes. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.commonFrameOffset_zero_eq_relative
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
    carrier.commonFrameOffset (0, 0) =
      macrocell.commonFrameOffset
        (macrocell.relativeShiftFrom carrier) := by
  rcases carrierShiftValue : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftValue : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteOccurrenceWitness.commonFrameOffset,
      FinalGaugedRouteMacrocellOccurrenceWitness.relativeShiftFrom,
      carrierMacroPeriodTranslation,
      carrierShiftValue, macrocellShiftValue,
      Cell.sub, Cell.scale]

/-- Translating the carrier into the direct frame and then normalizing the
crossover applies the same physical offset as normalizing the direct source. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.commonFrameOffset_normalizedCrossover_eq
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
    (crossing : CrossingRecord) :
    carrier.commonFrameOffset
        (carrier.normalizedCrossoverShift macrocell crossing) =
      macrocell.commonFrameOffset
        (Cell.neg
          (crossingPeriodShift formula.incidenceGraph crossing)) := by
  rcases carrierShiftValue : carrier.physicalShift with
    ⟨carrierShiftX, carrierShiftY⟩
  rcases macrocellShiftValue : macrocell.physicalShift with
    ⟨macrocellShiftX, macrocellShiftY⟩
  rcases crossingShiftValue :
      crossingPeriodShift formula.incidenceGraph crossing with
    ⟨crossingShiftX, crossingShiftY⟩
  apply Prod.ext <;>
    simp [FinalGaugedRouteOccurrenceWitness.commonFrameOffset,
      FinalGaugedCarrierRouteOccurrenceWitness.normalizedCrossoverShift,
      FinalGaugedCarrierRouteOccurrenceWitness.relativeShiftTo,
      carrierMacroPeriodTranslation,
      carrierShiftValue, macrocellShiftValue, crossingShiftValue,
      Cell.add, Cell.sub, Cell.neg, Cell.scale] <;>
    ring_nf <;> simp

end PeriodicOrthocrossing
end LeanTrominoes

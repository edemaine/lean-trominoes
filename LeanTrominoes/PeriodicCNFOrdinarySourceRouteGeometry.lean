/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceSelectedValues
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixOrderedFanSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRouteOrderSemantics
import LeanTrominoes.UnitRouteEndpointDisplacement

/-! # Selected headers and tails reconstruct ordinary source routes -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix FormulaShapeFigureNinePolarityRouteTail FormulaShapeFigureNineSourceTail
open ClauseProfilePolarityRouteOperation

def sourceFirstDirection (header : FormulaShapeFigureNinePolarityRouteHeader.Header) : AxisDirection :=
  match header.figurePrefix with
  | .local _ => .invalid
  | .inherited _ query => query.2.2.1.direction query.2.2.2

theorem selectedHeader_inherited (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) :
    ∃ query, (selectedHeader profile slot).figurePrefix = .inherited slot query := by
  have h := selectedHeader_slot profile slot active
  cases eq : (selectedHeader profile slot).figurePrefix with
  | «local» query => simp [inheritedSlot, eq] at h
  | inherited actual query =>
    have same : actual = slot := by
      cases operation : (selectedHeader profile slot).polarity.operation <;>
        simp [inheritedSlot, eq, operation] at h <;> exact h
    subst actual
    exact ⟨query, rfl⟩

private theorem descriptorDirection (profile : DirectedClauseProfile)
    (index : Fin (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
      (clauseProfile profile)).incidences.length) (slot : SourceLiteralSlot)
    (query : PlanarOneInThreeNoUnitsFigureNine.LocalExtendedDirectionQuery)
    (eq : descriptorAt profile index = .inherited slot query) :
    query.2.2.1.direction query.2.2.2 = (exitFanData profile).direction (sourceSlotFin slot) := by
  unfold descriptorAt at eq
  dsimp only at eq
  split at eq <;> cases eq
  rfl

theorem selectedRoute_ofClause {Variable : Type}
    (source : PositionedPeriodicCNF Variable) (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (index : Nat)
    (clause : PositionedPeriodicClause Variable) (lookup : source.clauses[index]? = some clause)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3)
    (slot : SourceLiteralSlot) (active : sourceSlotNat slot < clause.literals.length)
    (unitSteps : (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes
      index (sourceSlotNat slot)).IsChain AxisDirection.IsUnitAxisStep)
    (lengthGe : 2 ≤ (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes
      index (sourceSlotNat slot)).length) :
    sourceFirstDirection (selectedHeader (DirectedClauseProfile.ofClause routes index clause) slot) ::
      selectedTailDirections (orderedTailDirections routes index clause)
        (selectedHeader (DirectedClauseProfile.ofClause routes index clause) slot) =
      Gadget.unitSubdivisionDirections (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
        source placement routes index (sourceSlotNat slot)) := by
  let profile := DirectedClauseProfile.ofClause routes index clause
  have finiteActive : sourceSlotNat slot < profile.taggedLiterals.length := by
    rw [DirectedClauseProfile.ofClause_taggedLiterals routes index clause nonempty width]
    simpa only [annotatedLiterals, List.length_map, List.length_zipIdx] using active
  obtain ⟨query, prefixEq⟩ := selectedHeader_inherited profile slot finiteActive
  obtain ⟨descriptorIndex, descriptorEq⟩ := exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
    profile (selectedHeader profile slot) (selectedHeader_mem profile slot finiteActive)
  have first : sourceFirstDirection (selectedHeader profile slot) =
      AxisDirection.polylineFirstDirection (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
        source placement routes index (sourceSlotNat slot)) := by
    simp only [sourceFirstDirection, prefixEq]
    rw [descriptorDirection _ _ _ _ (descriptorEq.trans prefixEq)]
    have slotEq : (sourceSlotFin slot).val = sourceSlotNat slot := by cases slot <;> rfl
    simpa only [slotEq] using exitFanData_direction_ordered_ofClause source placement routes index clause lookup nonempty width
      (sourceSlotFin slot) (by simpa only [slotEq] using active)
  have tail := selectedTailDirections_descriptorAt_inherited_eq_canonicalRoute source placement routes index
    clause lookup nonempty width (selectedHeader profile slot).polarity descriptorIndex slot query
    (descriptorEq.trans prefixEq)
  rw [descriptorEq] at tail
  change sourceFirstDirection (selectedHeader profile slot) :: _ = _
  rw [first, tail]
  cases routeEq : PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes index
      (sourceSlotNat slot) with
  | nil => simp [routeEq] at lengthGe
  | cons first rest =>
    cases rest with
    | nil => simp [routeEq] at lengthGe
    | cons second rest =>
      exact DelimitedDirectionDisplacement.firstDirection_cons_tail first second rest (by simpa [routeEq] using unitSteps)

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection

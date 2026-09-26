/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceValueProjection
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPresentationSlotSemantics

/-! # Projected values follow the actual clockwise ordinary literals -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation PeriodicCNFStripReduction
open HorizontalRoutedRouteHeaderPresentationAtomScope

theorem slots_map_index (profile : DirectedClauseProfile) :
    (slots profile).map sourceSlotNat = List.range profile.taggedLiterals.length := by
  cases profile <;> rfl

theorem orderedValues_ofClause {Variable : Type} (value : PeriodicLiteral Variable → Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (index : Nat)
    (clause : PositionedPeriodicClause Variable) (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    orderedValues (DirectedClauseProfile.ofClause routes index clause) (clause.literals.map value) =
      (PositionedPeriodicCNF.orderClauseByRouteDirection routes index clause).literals.map value := by
  let profile := DirectedClauseProfile.ofClause routes index clause
  have lengthEq : profile.taggedLiterals.length = clause.literals.length := by
    rw [DirectedClauseProfile.ofClause_taggedLiterals routes index clause nonempty width]
    simp only [annotatedLiterals, List.length_map, List.length_zipIdx]
  let ordered := (PositionedPeriodicCNF.orderClauseByRouteDirection routes index clause).literals.map value
  have lookupEq (slot : SourceLiteralSlot) (member : slot ∈ slots profile) :
      (clause.literals.map value).getD (sourceSlotNat (presentationSlotAt profile slot)) 0 =
        ordered.getD (sourceSlotNat slot) 0 := by
    have active : sourceSlotNat slot < clause.literals.length := by
      rw [← lengthEq]
      exact (slots_active profile slot).1 member
    have h := orderClause_literal_lookup_at_presentationSlot routes index clause nonempty width slot active
    simpa only [ordered, profile, List.getD_eq_getElem?_getD, List.getElem?_map] using
      (congrArg (fun literal => (literal.map value).getD 0) h).symm
  change (slots profile).map _ = ordered
  rw [List.map_congr_left lookupEq]
  calc
    _ = (List.range clause.literals.length).map (fun i => ordered.getD i 0) := by
      rw [← lengthEq, ← slots_map_index profile, List.map_map]
      rfl
    _ = ordered := by
      have len : ordered.length = clause.literals.length := by
        simp only [ordered, List.length_map, PositionedPeriodicCNF.orderClauseByRouteDirection_length]
      rw [← len]
      exact List.map_range_getD ordered 0

theorem orderedValueBlocks_eq (blocks : List ValueBlock) :
    blocks.flatMap (fun block => orderedValues block.1 block.2.literals) =
      (List.zipWith orderedValues (blocks.map Prod.fst) (blocks.map (fun block => block.2.literals))).flatten := by
  rw [List.zipWith_map, List.zipWith_self, ← List.flatMap_def]

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection

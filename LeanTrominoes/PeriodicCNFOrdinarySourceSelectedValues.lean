/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceQueries
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceAtomValueRows

/-! # Selected ordinary records preserve their inherited literal values -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation FormulaShapeFigureNineRoutePrefix
open PeriodicCNFStripReduction
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

theorem inheritedSlot_scope (profile : DirectedClauseProfile) (header : Header)
    (member : header ∈ sourceClauseHeaders profile) (slot : SourceLiteralSlot)
    (selected : inheritedSlot header = some slot) :
    outputAtomScopeControl header = .inherited slot := by
  have classified := sourceSlot_header profile header member
  rcases header with ⟨⟨polaritySlot, operation⟩, descriptor⟩
  cases descriptor with
  | «local» query => cases operation <;> simp [inheritedSlot] at selected
  | inherited actual query =>
    have classification : sourceSlot? (prefixAtom (.inherited actual query)) = some actual := classified
    cases operation <;> simp only [inheritedSlot, Option.some.injEq] at selected
    all_goals first
      | contradiction
      | subst actual
        rw [outputAtomScopeControl_eq]
        simp only [outputParentRelativeAtom, ParentRelativeAtom.inheritedSourceSlot?, classification]

theorem selectedHeader_scope (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) :
    remapScopeControl profile (outputAtomScopeControl (selectedHeader profile slot)) =
      .inherited (presentationSlotAt profile slot) := by
  rw [inheritedSlot_scope profile _ (selectedHeader_mem profile slot active) slot
    (selectedHeader_slot profile slot active)]
  rfl

theorem selectedValue (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) (row : SourceOccurrenceAtomValueRow) :
    ((clauseBlock profile).map row.value).getD (selectedIndex profile slot) 0 =
      row.literals.getD (sourceSlotNat (presentationSlotAt profile slot)) 0 := by
  have bound := selectedIndex_lt profile slot active
  unfold clauseBlock
  rw [List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using selectedIndex_lt profile slot active)]
  rw [List.getElem_map]
  change row.value (remapScopeControl profile (outputAtomScopeControl
    ((sourceClauseHeaders profile)[selectedIndex profile slot]))) = _
  have headerEq : (sourceClauseHeaders profile)[selectedIndex profile slot] = selectedHeader profile slot := by
    rw [selectedHeader, List.getD_eq_getElem _ _ (selectedIndex_lt profile slot active)]
  rw [headerEq, selectedHeader_scope profile slot active]
  rfl

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection

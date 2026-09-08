/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FirstParentInheritedRouteCompiler
import LeanTrominoes.UnaryFieldBooleanFilterCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceAtomValueRows
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs

/-! # First-parent route selection preserves the same header, atom, and tail -/

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope

private theorem selected_false {Value : Type} (values : List Value) :
    DelimitedBinaryWordBooleanFilter.selected (List.replicate values.length false) values = [] := by
  induction values with
  | nil => rfl
  | cons value values induction => simpa [DelimitedBinaryWordBooleanFilter.selected, List.replicate_succ] using induction

private theorem selected_index {Value : Type} (values : List Value) (index : Nat)
    (bound : index < values.length) :
    DelimitedBinaryWordBooleanFilter.selected
        ((List.range values.length).map fun row => decide (row = index)) values = [values[index]] := by
  induction values generalizing index with
  | nil => simp at bound
  | cons value values induction =>
    cases index with
    | zero =>
      simp [List.range_succ_eq_map, List.map_map, Function.comp_def,
        DelimitedBinaryWordBooleanFilter.selected, selected_false]
    | succ index =>
      have remaining := induction index (Nat.lt_of_succ_lt_succ bound)
      simpa [List.range_succ_eq_map, List.map_map, Function.comp_def,
        DelimitedBinaryWordBooleanFilter.selected] using remaining

/-- Exactly the datum attached to the chosen actual header is retained. -/
theorem selectedValues_headerMap (profile : DirectedClauseProfile) (value : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Nat) :
    UnaryFieldBooleanFilter.selectedValues (controls profile) ((sourceClauseHeaders profile).map value) =
      [value (selectedHeader profile)] := by
  rw [UnaryFieldBooleanFilter.selectedValues_eq, controls]
  have selected := selected_index ((sourceClauseHeaders profile).map value) (index profile)
    (by simpa only [List.length_map] using index_lt profile)
  rw [List.getElem_map] at selected
  rw [selectedHeader, List.getD_eq_getElem _ _ (index_lt profile)]
  simpa only [List.length_map] using selected

theorem selectedHeader_scope (profile : DirectedClauseProfile) :
    remapScopeControl profile (outputAtomScopeControl (selectedHeader profile)) = .inherited .first := by
  have active := selectedHeader_eligible profile
  cases prefixEq : (selectedHeader profile).figurePrefix with
  | «local» query => simp [eligible, prefixEq] at active
  | inherited slot query =>
    have properties : presentationSlotAt profile slot = .first ∧
        remapScopeControl profile (outputAtomScopeControl (selectedHeader profile)) = .inherited .first := by
      simpa [eligible, prefixEq] using active
    exact properties.2

/-- The selected header consumes the source route for the same first literal. -/
theorem selectedHeader_inherited (profile : DirectedClauseProfile) :
    ∃ slot query, (selectedHeader profile).figurePrefix = .inherited slot query ∧
      presentationSlotAt profile slot = .first := by
  have active := selectedHeader_eligible profile
  cases prefixEq : (selectedHeader profile).figurePrefix with
  | «local» query => simp [eligible, prefixEq] at active
  | inherited slot query =>
    refine ⟨slot, query, rfl, ?_⟩
    have properties : presentationSlotAt profile slot = .first ∧
        remapScopeControl profile (outputAtomScopeControl (selectedHeader profile)) = .inherited .first := by
      simpa [eligible, prefixEq] using active
    exact properties.1

/-- The selected row takes the first source literal's value, regardless of
unused parent-local fallbacks elsewhere in the block. -/
theorem selectedValues_literalRow (profile : DirectedClauseProfile) (row : SourceOccurrenceAtomValueRow) :
    UnaryFieldBooleanFilter.selectedValues (controls profile) ((clauseBlock profile).map row.value) =
      [row.literals.getD 0 0] := by
  unfold clauseBlock
  rw [List.map_map]
  rw [selectedValues_headerMap]
  simp only [Function.comp_def, selectedHeader_scope, SourceOccurrenceAtomValueRow.value, sourceSlotNat]

/-- Tail selection uses the identical header chosen for the inherited atom. -/
theorem selectedValues_tailRow (profile : DirectedClauseProfile)
    (tails : List (List AxisDirection)) (value : List AxisDirection → Nat) :
    UnaryFieldBooleanFilter.selectedValues (controls profile)
        ((sourceClausePairs profile tails).map fun pair => value pair.2) =
      [value (selectedTailDirections tails (selectedHeader profile))] := by
  unfold sourceClausePairs
  rw [List.map_map]
  exact selectedValues_headerMap profile (fun header => value (selectedTailDirections tails header))

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute

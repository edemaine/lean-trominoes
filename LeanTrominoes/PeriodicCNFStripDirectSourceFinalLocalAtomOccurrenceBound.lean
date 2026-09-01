/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderGlobalLocalAtomCodeSemantics

/-! # Direct final parent-local atom occurrence bound -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem finalAtomScopeBit_remapScopeControl
    (profile : DirectedClauseProfile) (scope : AtomScopeControl) :
    finalAtomScopeBit
        (HorizontalRoutedRouteHeaderPresentationAtomScope.remapScopeControl
          profile scope) =
      finalAtomScopeBit scope := by
  cases scope <;> rfl

/-- Presentation-relative remapping changes an inherited slot's name, but
not whether the occurrence is inherited or parent-local. -/
theorem presentationScopeBits_eq_occurrenceScopeBits
    (source : List Token) :
    (HorizontalRoutedRouteHeaderPresentationAtomScope.output source).map
        finalAtomScopeBit =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).map
        (fun occurrence => finalAtomScopeBit occurrence.atomScopeControl) := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            HorizontalRoutedRouteHeaderOccurrenceBlock.output,
            HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock] using
              induction
      | clause profile =>
          simp only [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderOccurrenceBlock.output,
            List.flatMap_cons, List.map_append,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock]
          apply congrArg₂ (List.append)
          · unfold HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro header headerMember
            simp only [Function.comp_apply,
              occurrenceData_atomScopeControl]
            exact finalAtomScopeBit_remapScopeControl profile _
          · exact induction

/-- The direct scope-bit compiler is the presentation-relative descriptor
scope classification, because that remapping preserves the scope branch. -/
theorem directSourceFinalAtomScopeBits_eq_presentation
    (symbols : List encoding.Γ) :
    directSourceFinalAtomScopeBits decider symbols =
      (HorizontalRoutedRouteHeaderPresentationAtomScope.output
        (directSourceFinalClauseDescriptors decider symbols)).map
          finalAtomScopeBit := by
  rw [directSourceFinalAtomScopeBits_eq_map,
    directSourceFinalAtomScopeControls_eq_map,
    ← directSourceFinalClauseDescriptors_occurrenceData_eq,
    List.map_map]
  exact
    (presentationScopeBits_eq_occurrenceScopeBits
      (directSourceFinalClauseDescriptors decider symbols)).symm

private theorem selectedLocalCodes_eq_booleanSelected
    (scopes : List AtomScopeControl) (values : List Nat) :
    HorizontalRoutedRouteHeaderGlobalLocalAtomCode.selectedLocalCodes
        scopes values =
      DelimitedBinaryWordBooleanFilter.selected
        (scopes.map finalAtomScopeBit) values := by
  induction scopes generalizing values with
  | nil => rfl
  | cons scope scopes induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases scope <;>
            simp [HorizontalRoutedRouteHeaderGlobalLocalAtomCode.selectedLocalCodes,
              DelimitedBinaryWordBooleanFilter.selected,
              finalAtomScopeBit, induction]

/-- Selecting the direct local-code column by the actual final scope bits is
exactly the semantic parent-local selection over the descriptor compiler. -/
theorem directSourceFinalSelectedLocalAtomCodes_eq
    (symbols : List encoding.Γ) :
    DelimitedBinaryWordBooleanFilter.selected
        (directSourceFinalAtomScopeBits decider symbols)
        (directSourceFinalLocalAtomCodes decider symbols) =
      HorizontalRoutedRouteHeaderGlobalLocalAtomCode.selectedLocalCodes
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output
          (directSourceFinalClauseDescriptors decider symbols))
        (HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes
          (directSourceFinalClauseDescriptors decider symbols)) := by
  rw [directSourceFinalAtomScopeBits_eq_presentation]
  unfold directSourceFinalLocalAtomCodes
  exact (selectedLocalCodes_eq_booleanSelected _ _).symm

/-- Every direct parent-local final atom code occurs at most three times in
the positions at which the final identity compiler selects that namespace. -/
theorem directSourceFinalSelectedLocalAtomCodes_count_le_three
    (symbols : List encoding.Γ) (target : Nat) :
    (DelimitedBinaryWordBooleanFilter.selected
      (directSourceFinalAtomScopeBits decider symbols)
      (directSourceFinalLocalAtomCodes decider symbols)).count target <= 3 := by
  rw [directSourceFinalSelectedLocalAtomCodes_eq]
  exact
    HorizontalRoutedRouteHeaderGlobalLocalAtomCode.selectedLocalCodes_codes_count_le_three
      (directSourceFinalClauseDescriptors decider symbols) target

end PeriodicCNFStripReduction
end LeanTrominoes

end

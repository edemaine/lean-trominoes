/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeOccurrenceBound

/-! # Occurrence bound for all direct final inherited ring codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open HorizontalRoutedRouteHeaderInheritedSourceSelection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Expanding the cycle descriptor suffix's presentation scopes gives the
same fixed local table once per distinct retained-source identity. -/
theorem directSourceFinalCyclePresentationAtomScopeControls_eq_output
    (symbols : List encoding.Γ) :
    directSourceFinalCyclePresentationAtomScopeControls decider symbols =
      HorizontalRoutedRouteHeaderPresentationAtomScope.output
        (directSourceFinalCycleClauseDescriptors decider symbols) := by
  unfold directSourceFinalCyclePresentationAtomScopeControls
    directSourceFinalCycleClauseDescriptors
    HorizontalRoutedRouteHeaderPresentationAtomScope.output
  rw [List.flatMap_assoc,
    directRetainedFigureNineFiniteSourceVariableMarkers_eq_replicate_identities]
  induction directSourceFinalDistinctAtomIdentityIndices decider symbols with
  | nil => rfl
  | cons identity identities induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.flatMap_cons]
      change (directSourceFinalLocalCyclePresentationAtomScopeControls ++ _) =
        (directSourceFinalLocalCyclePresentationAtomScopeControls ++ _)
      rw [induction]

/-- Complete presentation-relative scopes split in the same copied-plus-cycle
order as the inherited ring-code compiler. -/
theorem directSourceFinalPresentationAtomScopeControls_eq_copied_cycle
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteHeaderPresentationAtomScope.output
        (directSourceFinalClauseDescriptors decider symbols) =
      directSourceFinalCopiedPresentationAtomScopeControls decider symbols ++
        directSourceFinalCyclePresentationAtomScopeControls decider symbols := by
  unfold directSourceFinalClauseDescriptors
    directSourceFinalCopiedPresentationAtomScopeControls
    HorizontalRoutedRouteHeaderPresentationAtomScope.output
  rw [List.flatMap_append,
    directSourceFinalCyclePresentationAtomScopeControls_eq_output]
  rfl

/-- Selecting the complete inherited code column splits into the already
analyzed copied and implication-cycle subsequences. -/
theorem directSourceFinalSelectedInheritedRingAtomCodes_eq_copied_cycle
    (symbols : List encoding.Γ) :
    selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output
          (directSourceFinalClauseDescriptors decider symbols))
        (directSourceFinalInheritedRingAtomCodes decider symbols) =
      selectedInheritedValues
          (directSourceFinalCopiedPresentationAtomScopeControls decider symbols)
          (directSourceFinalCopiedInheritedRingAtomCodes decider symbols) ++
        selectedInheritedValues
          (directSourceFinalCyclePresentationAtomScopeControls decider symbols)
          (directSourceFinalCycleInheritedRingAtomCodes decider symbols) := by
  rw [directSourceFinalPresentationAtomScopeControls_eq_copied_cycle]
  unfold directSourceFinalInheritedRingAtomCodes
  apply selectedInheritedValues_append
  exact (directSourceFinalCopiedPresentationAtomScopeControls_length
    decider symbols).trans
      (directSourceFinalCopiedInheritedRingAtomCodes_length
        decider symbols).symm

/-- The copied phase contributes at most one occurrence and the cycle phase
at most two, so every selected inherited base-nine code occurs at most three
times in the complete final occurrence stream. -/
theorem directSourceFinalSelectedInheritedRingAtomCodes_count_le_three
    (symbols : List encoding.Γ) (target : Nat) :
    (selectedInheritedValues
      (HorizontalRoutedRouteHeaderPresentationAtomScope.output
        (directSourceFinalClauseDescriptors decider symbols))
      (directSourceFinalInheritedRingAtomCodes
        decider symbols)).count target <= 3 := by
  rw [directSourceFinalSelectedInheritedRingAtomCodes_eq_copied_cycle,
    List.count_append]
  have copiedLe :
      (selectedInheritedValues
        (directSourceFinalCopiedPresentationAtomScopeControls decider symbols)
        (directSourceFinalCopiedInheritedRingAtomCodes
          decider symbols)).count target <= 1 :=
    (List.nodup_iff_count_le_one.mp
      (directSourceFinalCopiedSelectedInheritedRingAtomCodes_nodup
        decider symbols)) target
  have cycleLe :=
    directSourceFinalCycleSelectedInheritedRingAtomCodes_count_le_two
      decider symbols target
  omega

private theorem evenInheritedCode_injective :
    Function.Injective (fun code : Nat => code * 2) := by
  intro first second equality
  apply Nat.mul_left_cancel (by omega : 0 < 2)
  simpa [Nat.mul_comm] using equality

/-- The injective even-namespace map preserves the at-most-three inherited
occurrence bound. -/
theorem directSourceFinalSelectedEvenInheritedAtomCodes_count_le_three
    (symbols : List encoding.Γ) (target : Nat) :
    (selectedInheritedValues
      (HorizontalRoutedRouteHeaderPresentationAtomScope.output
        (directSourceFinalClauseDescriptors decider symbols))
      (directSourceFinalEvenInheritedAtomCodes
        decider symbols)).count target <= 3 := by
  rw [directSourceFinalEvenInheritedAtomCodes_eq_map,
    selectedInheritedValues_map]
  by_cases targetMember : target ∈
      (selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output
          (directSourceFinalClauseDescriptors decider symbols))
        (directSourceFinalInheritedRingAtomCodes decider symbols)).map
          fun code => code * 2
  · rcases List.mem_map.mp targetMember with ⟨code, codeMember, rfl⟩
    rw [List.count_map_of_injective _ _ evenInheritedCode_injective code]
    exact directSourceFinalSelectedInheritedRingAtomCodes_count_le_three
      decider symbols code
  · rw [List.count_eq_zero.mpr targetMember]
    omega

end LeanTrominoes.PeriodicCNFStripReduction

end

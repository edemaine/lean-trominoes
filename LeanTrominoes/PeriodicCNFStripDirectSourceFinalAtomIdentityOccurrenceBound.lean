/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceOccurrenceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedRingAtomCodeOccurrenceBound
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalLocalAtomOccurrenceBound

/-! # Occurrence bound for complete direct final atom identities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderInheritedSourceSelection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem booleanSelectedNot_finalAtomScopeBit_eq_selectedInheritedValues
    (scopes : List AtomScopeControl) (values : List Nat) :
    DelimitedBinaryWordBooleanFilter.selected
        ((scopes.map finalAtomScopeBit).map Bool.not) values =
      selectedInheritedValues scopes values := by
  induction scopes generalizing values with
  | nil => rfl
  | cons scope scopes induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases scope with
          | inherited sourceSlot =>
              change value ::
                  DelimitedBinaryWordBooleanFilter.selected
                    ((scopes.map finalAtomScopeBit).map Bool.not) values =
                value :: selectedInheritedValues scopes values
              rw [induction values]
          | parentLocal control =>
              change DelimitedBinaryWordBooleanFilter.selected
                    ((scopes.map finalAtomScopeBit).map Bool.not) values =
                selectedInheritedValues scopes values
              exact induction values

/-- False controls in the actual final scope-bit column select exactly the
presentation-relative inherited occurrences. -/
theorem directSourceFinalSelectedFalseEvenInheritedAtomCodes_eq
    (symbols : List encoding.Γ) :
    DelimitedBinaryWordBooleanFilter.selected
        ((directSourceFinalAtomScopeBits decider symbols).map Bool.not)
        (directSourceFinalEvenInheritedAtomCodes decider symbols) =
      selectedInheritedValues
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output
          (directSourceFinalClauseDescriptors decider symbols))
        (directSourceFinalEvenInheritedAtomCodes decider symbols) := by
  rw [directSourceFinalAtomScopeBits_eq_presentation]
  exact booleanSelectedNot_finalAtomScopeBit_eq_selectedInheritedValues _ _

/-- Every numeric identity emitted by the complete direct final identity
compiler occurs at most three times.  Even inherited and odd parent-local
namespaces are handled by their respective selected-column bounds. -/
theorem directSourceFinalAtomIdentityCodes_count_le_three
    (symbols : List encoding.Γ) (target : Nat) :
    (directSourceFinalAtomIdentityCodes decider symbols).count target <= 3 := by
  unfold directSourceFinalAtomIdentityCodes
  rw [AlignedUnaryBooleanChoice.selectedValues_count_eq_selected_branches
    (directSourceFinalAtomScopeBits decider symbols)
    (directSourceFinalEvenInheritedAtomCodes decider symbols)
    (directSourceFinalOddLocalAtomCodes decider symbols)
    ((directSourceFinalAtomScopeBits_length decider symbols).trans
      (directSourceFinalEvenInheritedAtomCodes_length
        decider symbols).symm)
    ((directSourceFinalEvenInheritedAtomCodes_length decider symbols).trans
      (directSourceFinalOddLocalAtomCodes_length decider symbols).symm)
    target]
  by_cases targetEven : ∃ code, target = code * 2
  · rcases targetEven with ⟨code, rfl⟩
    have oddNotMember : code * 2 ∉
        DelimitedBinaryWordBooleanFilter.selected
          (directSourceFinalAtomScopeBits decider symbols)
          (directSourceFinalOddLocalAtomCodes decider symbols) := by
      rw [directSourceFinalSelectedOddLocalAtomCodes_eq_map]
      intro member
      rcases List.mem_map.mp member with
        ⟨localCode, localCodeMember, encodedEq⟩
      omega
    rw [List.count_eq_zero.mpr oddNotMember, Nat.add_zero]
    rw [directSourceFinalSelectedFalseEvenInheritedAtomCodes_eq]
    exact directSourceFinalSelectedEvenInheritedAtomCodes_count_le_three
      decider symbols (code * 2)
  · have evenNotMember : target ∉
        DelimitedBinaryWordBooleanFilter.selected
          ((directSourceFinalAtomScopeBits decider symbols).map Bool.not)
          (directSourceFinalEvenInheritedAtomCodes decider symbols) := by
      rw [directSourceFinalSelectedFalseEvenInheritedAtomCodes_eq,
        directSourceFinalEvenInheritedAtomCodes_eq_map,
        selectedInheritedValues_map]
      intro member
      rcases List.mem_map.mp member with
        ⟨code, codeMember, encodedEq⟩
      exact targetEven ⟨code, encodedEq.symm⟩
    rw [List.count_eq_zero.mpr evenNotMember, Nat.zero_add]
    exact directSourceFinalSelectedOddLocalAtomCodes_count_le_three
      decider symbols target

end LeanTrominoes.PeriodicCNFStripReduction

end

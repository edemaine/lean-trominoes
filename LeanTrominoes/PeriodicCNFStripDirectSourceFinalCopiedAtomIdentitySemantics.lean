/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedAtomIdentityCompiler

/-! # Semantics of direct copied final atom identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled Boolean column is ordinary pointwise scope classification. -/
theorem directSourceFinalCopiedAtomScopeBits_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedAtomScopeBits decider symbols =
      (directSourceFinalCopiedPresentationAtomScopeControls
        decider symbols).map copiedAtomScopeBit := by
  unfold directSourceFinalCopiedAtomScopeBits
  induction directSourceFinalCopiedPresentationAtomScopeControls
      decider symbols with
  | nil => rfl
  | cons control controls induction => simp [induction]

/-- The inherited namespace is exactly twice each base-nine ring code. -/
theorem directSourceFinalCopiedEvenInheritedAtomCodes_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedEvenInheritedAtomCodes decider symbols =
      (directSourceFinalCopiedInheritedRingAtomCodes decider symbols).map
        fun code => code * 2 := by
  rfl

private theorem sums_scaled_ones
    (codes : List Nat) :
    UnaryAlignedAddMachine.sums
        (codes.map fun code => code * 2)
        (codes.map fun _ => 1) =
      codes.map fun code => code * 2 + 1 := by
  induction codes with
  | nil => rfl
  | cons code codes induction =>
      change (code * 2 + 1) ::
          UnaryAlignedAddMachine.sums
            (codes.map fun code => code * 2)
            (codes.map fun _ => 1) =
        (code * 2 + 1) :: codes.map (fun code => code * 2 + 1)
      rw [induction]

/-- The local namespace is exactly twice each parent-local code plus one. -/
theorem directSourceFinalCopiedOddLocalAtomCodes_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedOddLocalAtomCodes decider symbols =
      (directSourceFinalCopiedLocalAtomCodes decider symbols).map
        fun code => code * 2 + 1 := by
  unfold directSourceFinalCopiedOddLocalAtomCodes
    directSourceFinalCopiedScaledLocalAtomCodes
    UnaryFieldConstantScale.values UnaryFieldConstantStreams.ones
    AlignedUnaryListClosure.added
  exact sums_scaled_ones _

/-- The parity namespaces of inherited and parent-local identities are
disjoint. -/
theorem copiedEvenInherited_ne_oddLocal
    (inherited localCode : Nat) :
    inherited * 2 ≠ localCode * 2 + 1 := by
  omega

/-- At every copied occurrence, the complete identity is exactly the even
inherited ring code or odd parent-local code selected by its scope. -/
theorem directSourceFinalCopiedAtomIdentityCodes_getD
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directSourceFinalCopiedOccurrenceData decider symbols).length) :
    (directSourceFinalCopiedAtomIdentityCodes decider symbols).getD index 0 =
      if (directSourceFinalCopiedAtomScopeBits decider symbols).getD
          index false then
        (directSourceFinalCopiedOddLocalAtomCodes decider symbols).getD
          index 0
      else
        (directSourceFinalCopiedEvenInheritedAtomCodes decider symbols).getD
          index 0 := by
  generalize controlsEq :
      directSourceFinalCopiedAtomScopeBits decider symbols = controls
  generalize inheritedEq :
      directSourceFinalCopiedEvenInheritedAtomCodes decider symbols =
        inherited
  generalize localEq :
      directSourceFinalCopiedOddLocalAtomCodes decider symbols = localCodes
  have controlsLength :
      controls.length =
        (directSourceFinalCopiedOccurrenceData decider symbols).length := by
    rw [← controlsEq]
    exact directSourceFinalCopiedAtomScopeBits_length decider symbols
  have inheritedLength :
      inherited.length =
        (directSourceFinalCopiedOccurrenceData decider symbols).length := by
    rw [← inheritedEq]
    exact directSourceFinalCopiedEvenInheritedAtomCodes_length decider symbols
  have localLength :
      localCodes.length =
        (directSourceFinalCopiedOccurrenceData decider symbols).length := by
    rw [← localEq]
    exact directSourceFinalCopiedOddLocalAtomCodes_length decider symbols
  rw [directSourceFinalCopiedAtomIdentityCodes, controlsEq, inheritedEq,
    localEq]
  exact AlignedUnaryBooleanChoice.selectedValues_getD
    controls inherited localCodes
    (controlsLength.trans inheritedLength.symm)
    (inheritedLength.trans localLength.symm)
    index (by simpa [controlsLength] using indexLt)

end LeanTrominoes.PeriodicCNFStripReduction

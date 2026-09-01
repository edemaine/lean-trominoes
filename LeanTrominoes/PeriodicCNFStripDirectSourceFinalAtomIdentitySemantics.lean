/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityCompiler

/-! # Semantics of all direct final atom identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled Boolean column is ordinary pointwise final scope
classification. -/
theorem directSourceFinalAtomScopeBits_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalAtomScopeBits decider symbols =
      (directSourceFinalAtomScopeControls decider symbols).map
        finalAtomScopeBit := by
  unfold directSourceFinalAtomScopeBits
  induction directSourceFinalAtomScopeControls decider symbols with
  | nil => rfl
  | cons control controls induction => simp [induction]

/-- The inherited namespace is exactly twice each base-nine ring code. -/
theorem directSourceFinalEvenInheritedAtomCodes_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalEvenInheritedAtomCodes decider symbols =
      (directSourceFinalInheritedRingAtomCodes decider symbols).map
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

/-- The local namespace is exactly twice each globally parent-indexed code
plus one. -/
theorem directSourceFinalOddLocalAtomCodes_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalOddLocalAtomCodes decider symbols =
      (directSourceFinalLocalAtomCodes decider symbols).map
        fun code => code * 2 + 1 := by
  unfold directSourceFinalOddLocalAtomCodes
    directSourceFinalScaledLocalAtomCodes
    UnaryFieldConstantScale.values UnaryFieldConstantStreams.ones
    AlignedUnaryListClosure.added
  exact sums_scaled_ones _

/-- Inherited and parent-local final identities occupy disjoint parity
namespaces. -/
theorem finalEvenInherited_ne_oddLocal
    (inherited localCode : Nat) :
    inherited * 2 ≠ localCode * 2 + 1 := by
  omega

/-- At every final occurrence, the complete identity is exactly the even
inherited ring code or odd parent-local code selected by its scope. -/
theorem directSourceFinalAtomIdentityCodes_getD
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directSourceFinalCompiledOccurrenceData decider symbols).length) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
      if (directSourceFinalAtomScopeBits decider symbols).getD
          index false then
        (directSourceFinalOddLocalAtomCodes decider symbols).getD index 0
      else
        (directSourceFinalEvenInheritedAtomCodes decider symbols).getD
          index 0 := by
  generalize controlsEq :
      directSourceFinalAtomScopeBits decider symbols = controls
  generalize inheritedEq :
      directSourceFinalEvenInheritedAtomCodes decider symbols = inherited
  generalize localEq :
      directSourceFinalOddLocalAtomCodes decider symbols = localCodes
  have controlsLength :
      controls.length =
        (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← controlsEq]
    exact directSourceFinalAtomScopeBits_length decider symbols
  have inheritedLength :
      inherited.length =
        (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← inheritedEq]
    exact directSourceFinalEvenInheritedAtomCodes_length decider symbols
  have localLength :
      localCodes.length =
        (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← localEq]
    exact directSourceFinalOddLocalAtomCodes_length decider symbols
  rw [directSourceFinalAtomIdentityCodes, controlsEq, inheritedEq, localEq]
  exact AlignedUnaryBooleanChoice.selectedValues_getD
    controls inherited localCodes
    (controlsLength.trans inheritedLength.symm)
    (inheritedLength.trans localLength.symm)
    index (by simpa [controlsLength] using indexLt)

end LeanTrominoes.PeriodicCNFStripReduction

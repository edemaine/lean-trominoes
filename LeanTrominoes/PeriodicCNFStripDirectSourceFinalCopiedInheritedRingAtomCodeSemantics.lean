/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeCompiler

/-! # Semantics of direct copied inherited ring-atom codes -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Base nine separates the source-atom identity from any genuine ring
vertex slot. -/
theorem inheritedRingAtomCode_eq_iff
    (firstIdentity secondIdentity firstSlot secondSlot : Nat)
    (firstSlotLt : firstSlot < fixedEightRingVertexCount)
    (secondSlotLt : secondSlot < fixedEightRingVertexCount) :
    inheritedRingAtomCode firstIdentity firstSlot =
        inheritedRingAtomCode secondIdentity secondSlot ↔
      firstIdentity = secondIdentity ∧ firstSlot = secondSlot := by
  simp only [fixedEightRingVertexCount] at firstSlotLt secondSlotLt
  change firstIdentity * 9 + firstSlot =
      secondIdentity * 9 + secondSlot ↔
    firstIdentity = secondIdentity ∧ firstSlot = secondSlot
  omega

private theorem sums_scaled_eq_zipWith
    (identities slots : List Nat) :
    UnaryAlignedAddMachine.sums
        (UnaryFieldConstantScale.values fixedEightRingVertexCount identities)
        slots =
      List.zipWith inheritedRingAtomCode identities slots := by
  induction identities generalizing slots with
  | nil => rfl
  | cons identity identities induction =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          simp only [UnaryFieldConstantScale.values, List.map_cons,
            UnaryAlignedAddMachine.sums, List.zipWith_cons_cons,
            inheritedRingAtomCode]
          congr 1
          simpa [UnaryFieldConstantScale.values] using induction slots

/-- The compiled arithmetic is exactly pointwise pairing of inherited source
identity and copied terminal port. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      List.zipWith inheritedRingAtomCode
        (directSourceFinalCopiedInheritedAtomIdentityIndices decider symbols)
        (directSourceFinalCopiedTerminalSlotValues decider symbols) := by
  unfold directSourceFinalCopiedInheritedRingAtomCodes
    AlignedUnaryListClosure.added
    directSourceFinalCopiedScaledInheritedAtomIdentityIndices
  exact sums_scaled_eq_zipWith _ _

end LeanTrominoes.PeriodicCNFStripReduction

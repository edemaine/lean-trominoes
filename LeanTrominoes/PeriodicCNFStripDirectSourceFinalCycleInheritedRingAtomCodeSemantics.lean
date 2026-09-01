/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeSemantics

/-! # Semantics of direct final cycle inherited ring-atom codes -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

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

/-- Cycle inherited arithmetic is exactly pointwise source-identity/ring-slot
pairing in the common base-nine namespace. -/
theorem directSourceFinalCycleInheritedRingAtomCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedRingAtomCodes decider symbols =
      List.zipWith inheritedRingAtomCode
        (directSourceFinalCycleInheritedAtomIdentityIndices decider symbols)
        (directSourceFinalCycleRingVertexSlotValues decider symbols) := by
  unfold directSourceFinalCycleInheritedRingAtomCodes
    AlignedUnaryListClosure.added
    directSourceFinalCycleScaledInheritedAtomIdentityIndices
  exact sums_scaled_eq_zipWith _ _

/-- Every emitted cycle slot is genuinely within the common base-nine ring
namespace. -/
theorem directSourceFinalCycleRingVertexSlotValue_lt
    (symbols : List encoding.Γ) (slot : Nat)
    (member : slot ∈ directSourceFinalCycleRingVertexSlotValues
      decider symbols) :
    slot < fixedEightRingVertexCount := by
  unfold directSourceFinalCycleRingVertexSlotValues at member
  rcases List.mem_map.mp member with ⟨bounded, _, rfl⟩
  exact bounded.isLt

end LeanTrominoes.PeriodicCNFStripReduction

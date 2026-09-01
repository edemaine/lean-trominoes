/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleRingVertexSlotCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Inherited ring-atom codes of direct final cycle occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCycleInheritedRingCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalCycleScaledInheritedAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values fixedEightRingVertexCount
    (directSourceFinalCycleInheritedAtomIdentityIndices decider symbols)

/-- Base-nine source-identity/ring-vertex pairs at all inherited cycle
positions.  Values at parent-local positions are harmless and ignored. -/
def directSourceFinalCycleInheritedRingAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalCycleScaledInheritedAtomIdentityIndices decider symbols)
    (directSourceFinalCycleRingVertexSlotValues decider symbols)

@[simp] theorem
    directSourceFinalCycleScaledInheritedAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCycleScaledInheritedAtomIdentityIndices
      decider symbols).length =
      (directSourceFinalCycleOccurrenceData decider symbols).length := by
  unfold directSourceFinalCycleScaledInheritedAtomIdentityIndices
    UnaryFieldConstantScale.values
  rw [List.length_map,
    directSourceFinalCycleInheritedAtomIdentityIndices_length]

@[simp] theorem directSourceFinalCycleInheritedRingAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCycleInheritedRingAtomCodes decider symbols).length =
      (directSourceFinalCycleOccurrenceData decider symbols).length := by
  rw [directSourceFinalCycleInheritedRingAtomCodes,
    AlignedUnaryListClosure.added_length,
    directSourceFinalCycleScaledInheritedAtomIdentityIndices_length,
    directSourceFinalCycleRingVertexSlotValues_length, min_self]

noncomputable def
    directSourceFinalCycleScaledInheritedAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCycleScaledInheritedAtomIdentityIndices decider) := by
  unfold directSourceFinalCycleScaledInheritedAtomIdentityIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCycleInheritedAtomIdentityIndicesComputableInPolyTime
      decider)
    (UnaryFieldConstantScale.computableInPolyTime
      fixedEightRingVertexCount)

/-- Paired inherited cycle ring codes are polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalCycleInheritedRingAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCycleInheritedRingAtomCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCycleInheritedRingAtomCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalCycleScaledInheritedAtomIdentityIndices decider)
      (directSourceFinalCycleRingVertexSlotValues decider)
      (fun symbols =>
        (directSourceFinalCycleScaledInheritedAtomIdentityIndices_length
          decider symbols).trans
          (directSourceFinalCycleRingVertexSlotValues_length
            decider symbols).symm)
      (directSourceFinalCycleScaledInheritedAtomIdentityIndicesComputableInPolyTime
        decider)
      (directSourceFinalCycleRingVertexSlotValuesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

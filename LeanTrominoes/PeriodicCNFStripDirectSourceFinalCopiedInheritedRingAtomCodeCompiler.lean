/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedTerminalSlotSemantics
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Inherited ring-atom codes of direct copied final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedInheritedRingAtomCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The implication ring has eight copied ports and one separator vertex. -/
def fixedEightRingVertexCount : Nat := 9

/-- A source-atom identity paired with one vertex of its implication ring. -/
def inheritedRingAtomCode (identity terminalSlot : Nat) : Nat :=
  identity * fixedEightRingVertexCount + terminalSlot

def directSourceFinalCopiedScaledInheritedAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values fixedEightRingVertexCount
    (directSourceFinalCopiedInheritedAtomIdentityIndices decider symbols)

/-- Numeric ring-variable identities for the inherited positions of the
copied final occurrence prefix.  Values at parent-local positions remain
irrelevant. -/
def directSourceFinalCopiedInheritedRingAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalCopiedScaledInheritedAtomIdentityIndices
      decider symbols)
    (directSourceFinalCopiedTerminalSlotValues decider symbols)

theorem directSourceFinalCopiedScaledInheritedAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedScaledInheritedAtomIdentityIndices
      decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedScaledInheritedAtomIdentityIndices
    UnaryFieldConstantScale.values
  rw [List.length_map,
    directSourceFinalCopiedInheritedAtomIdentityIndices_length]

/-- The inherited ring-code column stays aligned with the exact copied
occurrence stream. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedInheritedRingAtomCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes,
    AlignedUnaryListClosure.added_length,
    directSourceFinalCopiedScaledInheritedAtomIdentityIndices_length,
    directSourceFinalCopiedTerminalSlotValues_length, min_self]

noncomputable def
    directSourceFinalCopiedScaledInheritedAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedScaledInheritedAtomIdentityIndices decider) := by
  unfold directSourceFinalCopiedScaledInheritedAtomIdentityIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCopiedInheritedAtomIdentityIndicesComputableInPolyTime
      decider)
    (UnaryFieldConstantScale.computableInPolyTime
      fixedEightRingVertexCount)

/-- The paired source-atom/port identities are polynomial-time computable as
unary fields, including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalCopiedInheritedRingAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedInheritedRingAtomCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedInheritedRingAtomCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalCopiedScaledInheritedAtomIdentityIndices decider)
      (directSourceFinalCopiedTerminalSlotValues decider)
      (fun symbols =>
        (directSourceFinalCopiedScaledInheritedAtomIdentityIndices_length
          decider symbols).trans
        (directSourceFinalCopiedTerminalSlotValues_length
          decider symbols).symm)
      (directSourceFinalCopiedScaledInheritedAtomIdentityIndicesComputableInPolyTime
        decider)
      (directSourceFinalCopiedTerminalSlotValuesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedLocalAtomCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedPresentationAtomScopeCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldConstantStreamCompiler

/-! # Globally scoped identities of direct copied final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedAtomIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- False selects an inherited ring variable; true selects a parent-local
auxiliary. -/
def copiedAtomScopeBit : AtomScopeControl → Bool
  | .inherited _ => false
  | .parentLocal _ => true

def directSourceFinalCopiedAtomScopeBits
    (symbols : List encoding.Γ) : List Bool :=
  (directSourceFinalCopiedPresentationAtomScopeControls
    decider symbols).flatMap fun control => [copiedAtomScopeBit control]

/-- Reserve the even namespace for inherited source-ring variables. -/
def directSourceFinalCopiedEvenInheritedAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 2
    (directSourceFinalCopiedInheritedRingAtomCodes decider symbols)

def directSourceFinalCopiedScaledLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 2
    (directSourceFinalCopiedLocalAtomCodes decider symbols)

/-- Reserve the odd namespace for parent-local auxiliaries. -/
def directSourceFinalCopiedOddLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalCopiedScaledLocalAtomCodes decider symbols)
    (UnaryFieldConstantStreams.ones
      (directSourceFinalCopiedLocalAtomCodes decider symbols))

/-- One globally scoped numeric identity per copied final occurrence. -/
def directSourceFinalCopiedAtomIdentityCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues
    (directSourceFinalCopiedAtomScopeBits decider symbols)
    (directSourceFinalCopiedEvenInheritedAtomCodes decider symbols)
    (directSourceFinalCopiedOddLocalAtomCodes decider symbols)

private theorem flatMap_singleton_length
    {Source Target : Type} (value : Source → Target)
    (source : List Source) :
    (source.flatMap fun item => [value item]).length = source.length := by
  induction source with
  | nil => rfl
  | cons item source induction => simp [induction]

@[simp] theorem directSourceFinalCopiedAtomScopeBits_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedAtomScopeBits decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  generalize controlsEq :
      directSourceFinalCopiedPresentationAtomScopeControls decider symbols =
        controls
  rw [directSourceFinalCopiedAtomScopeBits, controlsEq,
    flatMap_singleton_length]
  rw [← controlsEq]
  exact directSourceFinalCopiedPresentationAtomScopeControls_length
    decider symbols

@[simp] theorem directSourceFinalCopiedEvenInheritedAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedEvenInheritedAtomCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedEvenInheritedAtomCodes
    UnaryFieldConstantScale.values
  rw [List.length_map,
    directSourceFinalCopiedInheritedRingAtomCodes_length]

@[simp] theorem directSourceFinalCopiedScaledLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedScaledLocalAtomCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedScaledLocalAtomCodes
    UnaryFieldConstantScale.values
  rw [List.length_map, directSourceFinalCopiedLocalAtomCodes_length]

@[simp] theorem directSourceFinalCopiedOddLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedOddLocalAtomCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  rw [directSourceFinalCopiedOddLocalAtomCodes,
    AlignedUnaryListClosure.added_length,
    directSourceFinalCopiedScaledLocalAtomCodes_length]
  simp [UnaryFieldConstantStreams.ones,
    directSourceFinalCopiedLocalAtomCodes_length]

@[simp] theorem directSourceFinalCopiedAtomIdentityCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedAtomIdentityCodes decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
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
  rw [directSourceFinalCopiedAtomIdentityCodes, controlsEq, inheritedEq,
    localEq]
  rw [AlignedUnaryBooleanChoice.selectedValues,
    UnaryIndexedValueLookup.values_length,
    AlignedUnaryBooleanChoice.queries_length controls inherited
      (controlsLength.trans inheritedLength.symm)]
  exact controlsLength

noncomputable def directSourceFinalCopiedAtomScopeBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCopiedAtomScopeBits decider) := by
  let mapped := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCopiedPresentationAtomScopeControlsComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      fun control : AtomScopeControl => [copiedAtomScopeBit control])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    mapped (fun _ => rfl)

noncomputable def
    directSourceFinalCopiedEvenInheritedAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedEvenInheritedAtomCodes decider) := by
  unfold directSourceFinalCopiedEvenInheritedAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCopiedInheritedRingAtomCodesComputableInPolyTime decider)
    (UnaryFieldConstantScale.computableInPolyTime 2)

noncomputable def
    directSourceFinalCopiedScaledLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedScaledLocalAtomCodes decider) := by
  unfold directSourceFinalCopiedScaledLocalAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCopiedLocalAtomCodesComputableInPolyTime decider)
    (UnaryFieldConstantScale.computableInPolyTime 2)

noncomputable def
    directSourceFinalCopiedOddLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedOddLocalAtomCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedOddLocalAtomCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalCopiedScaledLocalAtomCodes decider)
      (fun symbols => UnaryFieldConstantStreams.ones
        (directSourceFinalCopiedLocalAtomCodes decider symbols))
      (fun symbols => by
        simp [UnaryFieldConstantStreams.ones,
          directSourceFinalCopiedScaledLocalAtomCodes_length,
          directSourceFinalCopiedLocalAtomCodes_length])
      (directSourceFinalCopiedScaledLocalAtomCodesComputableInPolyTime decider)
      (TM2CompositionMachine.computableInPolyTime
        (directSourceFinalCopiedLocalAtomCodesComputableInPolyTime decider)
        UnaryFieldConstantStreams.onesComputableInPolyTime)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- Complete copied-prefix identities are polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalCopiedAtomIdentityCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedAtomIdentityCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedAtomIdentityCodes
    exact AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime
      id
      (directSourceFinalCopiedAtomScopeBits decider)
      (directSourceFinalCopiedEvenInheritedAtomCodes decider)
      (directSourceFinalCopiedOddLocalAtomCodes decider)
      (fun symbols =>
        (directSourceFinalCopiedAtomScopeBits_length decider symbols).trans
          (directSourceFinalCopiedEvenInheritedAtomCodes_length
            decider symbols).symm)
      (fun symbols =>
        (directSourceFinalCopiedEvenInheritedAtomCodes_length
          decider symbols).trans
          (directSourceFinalCopiedOddLocalAtomCodes_length
            decider symbols).symm)
      (directSourceFinalCopiedAtomScopeBitsComputableInPolyTime decider)
      (directSourceFinalCopiedEvenInheritedAtomCodesComputableInPolyTime
        decider)
      (directSourceFinalCopiedOddLocalAtomCodesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

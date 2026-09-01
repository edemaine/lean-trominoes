/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomScopeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedRingAtomCodeCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldConstantStreamCompiler

/-! # Globally scoped identities of all direct final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAtomIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- False selects an inherited ring variable; true selects a globally
parent-indexed local auxiliary. -/
def finalAtomScopeBit : AtomScopeControl → Bool
  | .inherited _ => false
  | .parentLocal _ => true

def directSourceFinalAtomScopeBits
    (symbols : List encoding.Γ) : List Bool :=
  (directSourceFinalAtomScopeControls decider symbols).flatMap
    fun control => [finalAtomScopeBit control]

/-- Reserve the even namespace for inherited source-ring variables. -/
def directSourceFinalEvenInheritedAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 2
    (directSourceFinalInheritedRingAtomCodes decider symbols)

def directSourceFinalScaledLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 2
    (directSourceFinalLocalAtomCodes decider symbols)

/-- Reserve the odd namespace for parent-local auxiliaries. -/
def directSourceFinalOddLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalScaledLocalAtomCodes decider symbols)
    (UnaryFieldConstantStreams.ones
      (directSourceFinalLocalAtomCodes decider symbols))

/-- One globally scoped numeric identity per final occurrence. -/
def directSourceFinalAtomIdentityCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues
    (directSourceFinalAtomScopeBits decider symbols)
    (directSourceFinalEvenInheritedAtomCodes decider symbols)
    (directSourceFinalOddLocalAtomCodes decider symbols)

private theorem flatMap_singleton_length
    {Source Target : Type} (value : Source → Target)
    (source : List Source) :
    (source.flatMap fun item => [value item]).length = source.length := by
  induction source with
  | nil => rfl
  | cons item source induction => simp [induction]

@[simp] theorem directSourceFinalAtomScopeBits_length
    (symbols : List encoding.Γ) :
    (directSourceFinalAtomScopeBits decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  generalize controlsEq :
      directSourceFinalAtomScopeControls decider symbols = controls
  rw [directSourceFinalAtomScopeBits, controlsEq,
    flatMap_singleton_length]
  rw [← controlsEq, directSourceFinalAtomScopeControls_eq_map,
    List.length_map]

@[simp] theorem directSourceFinalEvenInheritedAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalEvenInheritedAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalEvenInheritedAtomCodes
    UnaryFieldConstantScale.values
  rw [List.length_map, directSourceFinalInheritedRingAtomCodes_length]

@[simp] theorem directSourceFinalScaledLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalScaledLocalAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalScaledLocalAtomCodes
    UnaryFieldConstantScale.values
  rw [List.length_map,
    directSourceFinalLocalAtomCodes_length_eq_occurrences]

@[simp] theorem directSourceFinalOddLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOddLocalAtomCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalOddLocalAtomCodes,
    AlignedUnaryListClosure.added_length,
    directSourceFinalScaledLocalAtomCodes_length]
  simp [UnaryFieldConstantStreams.ones,
    directSourceFinalLocalAtomCodes_length_eq_occurrences]

@[simp] theorem directSourceFinalAtomIdentityCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalAtomIdentityCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
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
  rw [directSourceFinalAtomIdentityCodes, controlsEq, inheritedEq, localEq]
  rw [AlignedUnaryBooleanChoice.selectedValues,
    UnaryIndexedValueLookup.values_length,
    AlignedUnaryBooleanChoice.queries_length controls inherited
      (controlsLength.trans inheritedLength.symm)]
  exact controlsLength

noncomputable def directSourceFinalAtomScopeBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalAtomScopeBits decider) := by
  let mapped := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalAtomScopeControlsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      fun control : AtomScopeControl => [finalAtomScopeBit control])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    mapped (fun _ => rfl)

noncomputable def
    directSourceFinalEvenInheritedAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalEvenInheritedAtomCodes decider) := by
  unfold directSourceFinalEvenInheritedAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalInheritedRingAtomCodesComputableInPolyTime decider)
    (UnaryFieldConstantScale.computableInPolyTime 2)

noncomputable def
    directSourceFinalScaledLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalScaledLocalAtomCodes decider) := by
  unfold directSourceFinalScaledLocalAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalLocalAtomCodesComputableInPolyTime decider)
    (UnaryFieldConstantScale.computableInPolyTime 2)

noncomputable def
    directSourceFinalOddLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOddLocalAtomCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOddLocalAtomCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalScaledLocalAtomCodes decider)
      (fun symbols => UnaryFieldConstantStreams.ones
        (directSourceFinalLocalAtomCodes decider symbols))
      (fun symbols => by
        simp [UnaryFieldConstantStreams.ones,
          directSourceFinalScaledLocalAtomCodes_length,
          directSourceFinalLocalAtomCodes_length_eq_occurrences])
      (directSourceFinalScaledLocalAtomCodesComputableInPolyTime decider)
      (TM2CompositionMachine.computableInPolyTime
        (directSourceFinalLocalAtomCodesComputableInPolyTime decider)
        UnaryFieldConstantStreams.onesComputableInPolyTime)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- Complete final atom identities are polynomial-time computable, including
for the formally possible empty source alphabet. -/
noncomputable def directSourceFinalAtomIdentityCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalAtomIdentityCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalAtomIdentityCodes
    exact AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime
      id
      (directSourceFinalAtomScopeBits decider)
      (directSourceFinalEvenInheritedAtomCodes decider)
      (directSourceFinalOddLocalAtomCodes decider)
      (fun symbols =>
        (directSourceFinalAtomScopeBits_length decider symbols).trans
          (directSourceFinalEvenInheritedAtomCodes_length
            decider symbols).symm)
      (fun symbols =>
        (directSourceFinalEvenInheritedAtomCodes_length
          decider symbols).trans
          (directSourceFinalOddLocalAtomCodes_length
            decider symbols).symm)
      (directSourceFinalAtomScopeBitsComputableInPolyTime decider)
      (directSourceFinalEvenInheritedAtomCodesComputableInPolyTime decider)
      (directSourceFinalOddLocalAtomCodesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

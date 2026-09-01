/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataTripleAssembler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceDataCompiler

/-! # Complete finite variable-fan records for final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalVariableFanDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Natural values of the finite fan count-predecessor column. -/
def directSourceFinalFanCountPredValues
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalOccurrenceCountPreds decider symbols).map Fin.val

/-- Repeat each count predecessor beside its three selected occurrence
records. -/
def directSourceFinalFanRepeatedCountPredValues
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldFixedCopies.values 3
    (directSourceFinalFanCountPredValues decider symbols)

/-- Add each repeated count predecessor as the reserved finite-decoder slot
of its selected occurrence-record role code. -/
def directSourceFinalFanOccurrencePairCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalFanSelectedOccurrenceCodes decider symbols)
    (directSourceFinalFanRepeatedCountPredValues decider symbols)

/-- Decode the aligned selected occurrence record and repeated fan count. -/
def directSourceFinalFanOccurrencePairs
    (symbols : List encoding.Γ) :
    List (FiniteRoleSlotUnaryDecoder.Pair FinalFanOccurrenceData) :=
  FiniteRoleSlotUnaryDecoder.pairs
    (Role := FinalFanOccurrenceData)
    (directSourceFinalFanOccurrencePairCodes decider symbols)

/-- One complete finite variable-fan record per final routed occurrence. -/
def directSourceFinalVariableFanData
    (symbols : List encoding.Γ) :
    List PeriodicPlanarOneInThreeToThreeDM.VariableRibbonFanData :=
  FinalFanDataTripleAssembler.output
    (directSourceFinalFanOccurrencePairs decider symbols)

@[simp] theorem directSourceFinalFanCountPredValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanCountPredValues decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  simp [directSourceFinalFanCountPredValues]

@[simp] theorem directSourceFinalFanRepeatedCountPredValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanRepeatedCountPredValues decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanRepeatedCountPredValues
    UnaryFieldFixedCopies.values
  simp [directSourceFinalFanCountPredValues_length, Nat.mul_comm]

@[simp] theorem directSourceFinalFanOccurrencePairCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanOccurrencePairCodes decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanOccurrencePairCodes
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalFanSelectedOccurrenceCodes_length,
    directSourceFinalFanRepeatedCountPredValues_length, min_self]

@[simp] theorem directSourceFinalFanOccurrencePairs_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanOccurrencePairs decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanOccurrencePairs
    FiniteRoleSlotUnaryDecoder.pairs
  rw [List.length_map,
    directSourceFinalFanOccurrencePairCodes_length]

@[simp] theorem directSourceFinalVariableFanData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableFanData decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalVariableFanData
  exact FinalFanDataTripleAssembler.output_length_of_length_eq
    (directSourceFinalFanOccurrencePairs decider symbols)
    (directSourceFinalCompiledOccurrenceData decider symbols).length
    (directSourceFinalFanOccurrencePairs_length decider symbols)

noncomputable def
    directSourceFinalFanCountPredValuesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanCountPredValues decider) := by
  unfold directSourceFinalFanCountPredValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceCountPredsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime Fin.val)

noncomputable def
    directSourceFinalFanRepeatedCountPredValuesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanRepeatedCountPredValues decider) := by
  unfold directSourceFinalFanRepeatedCountPredValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalFanCountPredValuesComputableInPolyTime decider)
    (UnaryFieldFixedCopies.computableInPolyTime 3)

/-- The paired occurrence-role/count-slot codes are polynomial-time
computable, including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalFanOccurrencePairCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanOccurrencePairCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalFanOccurrencePairCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalFanSelectedOccurrenceCodes decider)
      (directSourceFinalFanRepeatedCountPredValues decider)
      (fun symbols => by
        rw [directSourceFinalFanSelectedOccurrenceCodes_length,
          directSourceFinalFanRepeatedCountPredValues_length])
      (directSourceFinalFanSelectedOccurrenceCodesComputableInPolyTime
        decider)
      (directSourceFinalFanRepeatedCountPredValuesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def directSourceFinalFanOccurrencePairsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalFanOccurrencePairs decider) := by
  unfold directSourceFinalFanOccurrencePairs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalFanOccurrencePairCodesComputableInPolyTime decider)
    (FiniteRoleSlotUnaryDecoder.computableInPolyTime
      (Role := FinalFanOccurrenceData))

/-- Complete finite fan records are polynomial-time computable from direct
source symbols. -/
noncomputable def directSourceFinalVariableFanDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalVariableFanData decider) := by
  unfold directSourceFinalVariableFanData
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalFanOccurrencePairsComputableInPolyTime decider)
    FinalFanDataTripleAssembler.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

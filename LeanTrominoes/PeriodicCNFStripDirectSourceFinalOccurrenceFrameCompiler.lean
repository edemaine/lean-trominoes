/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceFrameDecoder
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanDataCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Complete finite frames for direct final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceFrameStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Unary mixed-radix variable-fan contributions. -/
def directSourceFinalOccurrenceFrameVariableFanBases
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values DirectFinalOccurrenceFrame.variableFanBase
    (directSourceFinalVariableFanData decider symbols)

/-- Unary mixed-radix clause-frame contributions. -/
def directSourceFinalOccurrenceFrameClauseBases
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values DirectFinalOccurrenceFrame.clauseFrameBase
    (directSourceFinalClauseFrames decider symbols)

/-- Low base-eight stable-slot values. -/
def directSourceFinalOccurrenceFrameSlotValues
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values DirectFinalOccurrenceFrame.occurrenceSlotValue
    (directSourceFinalOccurrenceSlots decider symbols)

/-- Add the aligned variable-fan and clause-frame role contributions. -/
def directSourceFinalOccurrenceFrameRoleBases
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalOccurrenceFrameVariableFanBases decider symbols)
    (directSourceFinalOccurrenceFrameClauseBases decider symbols)

/-- Complete mixed-radix codes, one per final routed occurrence. -/
def directSourceFinalOccurrenceFrameCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalOccurrenceFrameRoleBases decider symbols)
    (directSourceFinalOccurrenceFrameSlotValues decider symbols)

/-- Explicit mixed-radix decoding of the complete frame codes. -/
def directSourceFinalOccurrenceFramePairs
    (symbols : List encoding.Γ) :
    List DirectFinalOccurrenceFrame.EncodedPair :=
  FiniteIndexSlotUnaryDecoder.pairs
    (Fintype.card DirectFinalOccurrenceFrame.VariableFan *
      Fintype.card DirectFinalOccurrenceFrame.ClauseFrame)
    (directSourceFinalOccurrenceFrameCodes decider symbols)

/-- One complete finite frame per final routed occurrence. -/
def directSourceFinalOccurrenceFrames
    (symbols : List encoding.Γ) :
    List DirectFinalOccurrenceFrame.Data :=
  DirectFinalOccurrenceFrame.data
    (directSourceFinalOccurrenceFramePairs decider symbols)

@[simp] theorem directSourceFinalOccurrenceFrameVariableFanBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrameVariableFanBases
      decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrameVariableFanBases
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalVariableFanData_length]

@[simp] theorem directSourceFinalOccurrenceFrameClauseBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrameClauseBases decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrameClauseBases
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalClauseFrames_length]

@[simp] theorem directSourceFinalOccurrenceFrameSlotValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrameSlotValues decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrameSlotValues
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalOccurrenceSlots_length]

@[simp] theorem directSourceFinalOccurrenceFrameRoleBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrameRoleBases decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrameRoleBases
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalOccurrenceFrameVariableFanBases_length,
    directSourceFinalOccurrenceFrameClauseBases_length, min_self]

@[simp] theorem directSourceFinalOccurrenceFrameCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrameCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrameCodes
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalOccurrenceFrameRoleBases_length,
    directSourceFinalOccurrenceFrameSlotValues_length, min_self]

@[simp] theorem directSourceFinalOccurrenceFramePairs_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFramePairs decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  simp [directSourceFinalOccurrenceFramePairs,
    FiniteIndexSlotUnaryDecoder.pairs]

@[simp] theorem directSourceFinalOccurrenceFrames_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFrames decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceFrames
  rw [DirectFinalOccurrenceFrame.data_length,
    directSourceFinalOccurrenceFramePairs_length]

noncomputable def
    directSourceFinalOccurrenceFrameVariableFanBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceFrameVariableFanBases decider) := by
  unfold directSourceFinalOccurrenceFrameVariableFanBases
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalVariableFanDataComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      DirectFinalOccurrenceFrame.variableFanBase)

noncomputable def
    directSourceFinalOccurrenceFrameClauseBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceFrameClauseBases decider) := by
  unfold directSourceFinalOccurrenceFrameClauseBases
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFramesComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      DirectFinalOccurrenceFrame.clauseFrameBase)

noncomputable def
    directSourceFinalOccurrenceFrameSlotValuesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceFrameSlotValues decider) := by
  unfold directSourceFinalOccurrenceFrameSlotValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      DirectFinalOccurrenceFrame.occurrenceSlotValue)

noncomputable def
    directSourceFinalOccurrenceFrameRoleBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceFrameRoleBases decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOccurrenceFrameRoleBases
    exact AlignedUnaryListClosure.addedComputableInPolyTime id
      (directSourceFinalOccurrenceFrameVariableFanBases decider)
      (directSourceFinalOccurrenceFrameClauseBases decider)
      (fun symbols => by
        rw [directSourceFinalOccurrenceFrameVariableFanBases_length,
          directSourceFinalOccurrenceFrameClauseBases_length])
      (directSourceFinalOccurrenceFrameVariableFanBasesComputableInPolyTime
        decider)
      (directSourceFinalOccurrenceFrameClauseBasesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def directSourceFinalOccurrenceFrameCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceFrameCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOccurrenceFrameCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime id
      (directSourceFinalOccurrenceFrameRoleBases decider)
      (directSourceFinalOccurrenceFrameSlotValues decider)
      (fun symbols => by
        rw [directSourceFinalOccurrenceFrameRoleBases_length,
          directSourceFinalOccurrenceFrameSlotValues_length])
      (directSourceFinalOccurrenceFrameRoleBasesComputableInPolyTime
        decider)
      (directSourceFinalOccurrenceFrameSlotValuesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def directSourceFinalOccurrenceFramePairsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalOccurrenceFramePairs decider) := by
  unfold directSourceFinalOccurrenceFramePairs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceFrameCodesComputableInPolyTime decider)
    (FiniteIndexSlotUnaryDecoder.computableInPolyTime
      (Fintype.card DirectFinalOccurrenceFrame.VariableFan *
        Fintype.card DirectFinalOccurrenceFrame.ClauseFrame))

/-- Complete finite occurrence frames are polynomial-time computable from
the direct source symbols. -/
noncomputable def directSourceFinalOccurrenceFramesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalOccurrenceFrames decider) := by
  unfold directSourceFinalOccurrenceFrames
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceFramePairsComputableInPolyTime decider)
    DirectFinalOccurrenceFrame.dataComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceDataCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Global routed-incidence keys from grouped final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PlanarThreeDM

/-- Width of the variable triple block selected by one finite occurrence
record. -/
def directFinalOccurrenceTripleBlockWidth
    (data : FinalFanOccurrenceData) : Nat :=
  match data.kind with
  | .fixedRed => 7
  | .fixedGreen | .fixedBlue => 3

/-- Incidence-key offsets `3 * localTriple + color` for the routed RGB
triple inside one occurrence block. -/
def directFinalOccurrenceRoutedIncidenceKeyOffsets
    (data : FinalFanOccurrenceData) : List Nat :=
  match data.kind with
  | .fixedRed => [15, 19, 20]
  | .fixedGreen | .fixedBlue => [6, 7, 2]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedRoutedIncidenceKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalGroupedOccurrenceTripleBlockWidths
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalGroupedOccurrenceData decider symbols).map
    directFinalOccurrenceTripleBlockWidth

/-- Global variable-triple start of every grouped occurrence block. -/
def directSourceFinalGroupedOccurrenceTripleBlockStarts
    (symbols : List encoding.Γ) : List Nat :=
  PrefixSums.starts
    (directSourceFinalGroupedOccurrenceTripleBlockWidths decider symbols)

/-- Repeat the incidence-key base `3 * tripleStart` for RGB. -/
def directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldFixedCopies.values 3
    (UnaryFieldConstantScale.values 3
      (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols))

def directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalGroupedOccurrenceData decider symbols).flatMap
    directFinalOccurrenceRoutedIncidenceKeyOffsets

/-- Global `3 * tripleIndex + color` key for every routed occurrence
incidence, in grouped occurrence-major and RGB-minor order. -/
def directSourceFinalGroupedRoutedIncidenceKeys
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
      decider symbols)
    (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
      decider symbols)

@[simp] theorem directFinalOccurrenceRoutedIncidenceKeyOffsets_length
    (data : FinalFanOccurrenceData) :
    (directFinalOccurrenceRoutedIncidenceKeyOffsets data).length = 3 := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  cases kind <;> rfl

private theorem fixedCopiesThree_length (source : List Nat) :
    (UnaryFieldFixedCopies.values 3 source).length = 3 * source.length := by
  unfold UnaryFieldFixedCopies.values
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [List.flatMap_cons, List.length_append, List.length_replicate,
        induction, List.length_cons]
      omega

@[simp] theorem
    directSourceFinalGroupedOccurrenceTripleBlockWidths_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceTripleBlockWidths
      decider symbols).length =
      (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  simp [directSourceFinalGroupedOccurrenceTripleBlockWidths]

@[simp] theorem
    directSourceFinalGroupedOccurrenceTripleBlockStarts_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceTripleBlockStarts
      decider symbols).length =
      (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  simp [directSourceFinalGroupedOccurrenceTripleBlockStarts]

@[simp] theorem
    directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
      decider symbols).length =
      3 * (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  unfold directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
  rw [fixedCopiesThree_length]
  simp [UnaryFieldConstantScale.values,
    directSourceFinalGroupedOccurrenceTripleBlockStarts_length]

@[simp] theorem
    directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
      decider symbols).length =
      3 * (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  unfold directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
  rw [List.length_flatMap]
  simp [Nat.mul_comm]

noncomputable def
    directSourceFinalGroupedOccurrenceTripleBlockWidthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedOccurrenceTripleBlockWidths decider) := by
  unfold directSourceFinalGroupedOccurrenceTripleBlockWidths
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedOccurrenceDataComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      directFinalOccurrenceTripleBlockWidth)

noncomputable def
    directSourceFinalGroupedOccurrenceTripleBlockStartsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedOccurrenceTripleBlockStarts decider) := by
  unfold directSourceFinalGroupedOccurrenceTripleBlockStarts
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedOccurrenceTripleBlockWidthsComputableInPolyTime
      decider)
    UnaryPrefixSumsMachine.computableInPolyTime

noncomputable def
    directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
        decider) := by
  unfold directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalGroupedOccurrenceTripleBlockStartsComputableInPolyTime
        decider)
      (UnaryFieldConstantScale.computableInPolyTime 3))
    (UnaryFieldFixedCopies.computableInPolyTime 3)

noncomputable def
    directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsetsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
        decider) := by
  unfold directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedOccurrenceDataComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime
      directFinalOccurrenceRoutedIncidenceKeyOffsets)

/-- The three global routed-incidence keys per grouped occurrence are
polynomial-time computable. -/
noncomputable def
    directSourceFinalGroupedRoutedIncidenceKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedRoutedIncidenceKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedRoutedIncidenceKeys
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases decider)
      (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets decider)
      (fun symbols => by rw [
        directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases_length,
        directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets_length])
      (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBasesComputableInPolyTime
        decider)
      (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsetsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

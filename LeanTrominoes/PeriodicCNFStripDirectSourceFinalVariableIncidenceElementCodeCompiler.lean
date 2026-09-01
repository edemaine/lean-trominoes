/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalVariableElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceBaseBroadcastSemantics
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Canonical element codes for final variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalVariableIncidenceCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Finite controls selecting cyclic-successor occurrence keys. -/
def directSourceFinalVariableIncidenceNextControlColumn
    (symbols : List encoding.Γ) : List Bool :=
  directSourceFinalVariableIncidenceNextControls
    (directSourceFinalVariableIncidenceElementSelectors decider symbols)

/-- Finite controls selecting parent-clause indices. -/
def directSourceFinalVariableIncidenceParentControlColumn
    (symbols : List encoding.Γ) : List Bool :=
  directSourceFinalVariableIncidenceParentControls
    (directSourceFinalVariableIncidenceElementSelectors decider symbols)

/-- Canonical structural tags unpacked from the finite selector stream. -/
def directSourceFinalVariableIncidenceTagColumn
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalVariableIncidenceTags
    (directSourceFinalVariableIncidenceElementSelectors decider symbols)

/-- Select current or cyclic-successor occurrence identity at every variable
incidence. -/
def directSourceFinalVariableIncidenceSelectedOccurrenceKeys
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues
    (directSourceFinalVariableIncidenceNextControlColumn decider symbols)
    (directSourceFinalVariableIncidenceCurrentKeys decider symbols)
    (directSourceFinalVariableIncidenceNextKeys decider symbols)

/-- Select an occurrence identity or the parent-clause index at every
variable incidence. -/
def directSourceFinalVariableIncidenceSelectedIdentityBases
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryBooleanChoice.selectedValues
    (directSourceFinalVariableIncidenceParentControlColumn decider symbols)
    (directSourceFinalVariableIncidenceSelectedOccurrenceKeys
      decider symbols)
    (directSourceFinalVariableIncidenceParentIndices decider symbols)

/-- Reserve the common 32-tag structural block beneath every selected
identity. -/
def directSourceFinalVariableIncidenceScaledIdentityBases
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values directSourceFinalElementCodeStride
    (directSourceFinalVariableIncidenceSelectedIdentityBases decider symbols)

/-- Complete canonical element code referenced by every grouped variable
incidence, aligned with the direction-query stream. -/
def directSourceFinalVariableIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalVariableIncidenceScaledIdentityBases decider symbols)
    (directSourceFinalVariableIncidenceTagColumn decider symbols)

@[simp] theorem directSourceFinalVariableIncidenceNextControlColumn_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceNextControlColumn
      decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceNextControlColumn]

@[simp] theorem directSourceFinalVariableIncidenceParentControlColumn_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceParentControlColumn
      decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceParentControlColumn]

@[simp] theorem directSourceFinalVariableIncidenceTagColumn_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceTagColumn decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceTagColumn]

@[simp] theorem
    directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceSelectedOccurrenceKeys
      decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  unfold directSourceFinalVariableIncidenceSelectedOccurrenceKeys
  have controlsFirst :
      (directSourceFinalVariableIncidenceNextControlColumn
        decider symbols).length =
        (directSourceFinalVariableIncidenceCurrentKeys
          decider symbols).length := by
    rw [directSourceFinalVariableIncidenceNextControlColumn_length,
      directSourceFinalVariableIncidenceCurrentKeys_length]
  rw [AlignedUnaryBooleanChoice.selectedValues_length
    _ _ _ controlsFirst,
    directSourceFinalVariableIncidenceNextControlColumn_length]

@[simp] theorem
    directSourceFinalVariableIncidenceSelectedIdentityBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceSelectedIdentityBases
      decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  unfold directSourceFinalVariableIncidenceSelectedIdentityBases
  have controlsFirst :
      (directSourceFinalVariableIncidenceParentControlColumn
        decider symbols).length =
        (directSourceFinalVariableIncidenceSelectedOccurrenceKeys
          decider symbols).length := by
    rw [directSourceFinalVariableIncidenceParentControlColumn_length,
      directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length]
  rw [AlignedUnaryBooleanChoice.selectedValues_length
    _ _ _ controlsFirst,
    directSourceFinalVariableIncidenceParentControlColumn_length]

@[simp] theorem
    directSourceFinalVariableIncidenceScaledIdentityBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceScaledIdentityBases
      decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceScaledIdentityBases,
    UnaryFieldConstantScale.values]

noncomputable def
    directSourceFinalVariableIncidenceNextControlColumnComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalVariableIncidenceNextControlColumn decider) := by
  unfold directSourceFinalVariableIncidenceNextControlColumn
  exact directSourceFinalVariableIncidenceNextControlsComputableInPolyTime
    decider

noncomputable def
    directSourceFinalVariableIncidenceParentControlColumnComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalVariableIncidenceParentControlColumn decider) := by
  unfold directSourceFinalVariableIncidenceParentControlColumn
  exact directSourceFinalVariableIncidenceParentControlsComputableInPolyTime
    decider

noncomputable def
    directSourceFinalVariableIncidenceTagColumnComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceTagColumn decider) := by
  unfold directSourceFinalVariableIncidenceTagColumn
  exact directSourceFinalVariableIncidenceTagsComputableInPolyTime decider

/-- The complete variable-incidence element-code column compiles in
polynomial time. -/
noncomputable def
    directSourceFinalVariableIncidenceElementCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceElementCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let occurrenceCompiler :=
      AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime
        id (directSourceFinalVariableIncidenceNextControlColumn decider)
        (directSourceFinalVariableIncidenceCurrentKeys decider)
        (directSourceFinalVariableIncidenceNextKeys decider)
        (fun symbols => by
          rw [directSourceFinalVariableIncidenceNextControlColumn_length,
            directSourceFinalVariableIncidenceCurrentKeys_length])
        (fun symbols => by
          rw [directSourceFinalVariableIncidenceCurrentKeys_length,
            directSourceFinalVariableIncidenceNextKeys_length])
        (directSourceFinalVariableIncidenceNextControlColumnComputableInPolyTime
          decider)
        (directSourceFinalVariableIncidenceCurrentKeysComputableInPolyTime
          decider)
        (directSourceFinalVariableIncidenceNextKeysComputableInPolyTime
          decider)
    let identityCompiler :=
      AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime
        id (directSourceFinalVariableIncidenceParentControlColumn decider)
        (directSourceFinalVariableIncidenceSelectedOccurrenceKeys decider)
        (directSourceFinalVariableIncidenceParentIndices decider)
        (fun symbols => by
          rw [directSourceFinalVariableIncidenceParentControlColumn_length,
            directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length])
        (fun symbols => by
          rw [directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length,
            directSourceFinalVariableIncidenceParentIndices_length])
        (directSourceFinalVariableIncidenceParentControlColumnComputableInPolyTime
          decider)
        occurrenceCompiler
        (directSourceFinalVariableIncidenceParentIndicesComputableInPolyTime
          decider)
    let scaledCompiler := TM2CompositionMachine.computableInPolyTime
      identityCompiler
      (UnaryFieldConstantScale.computableInPolyTime
        directSourceFinalElementCodeStride)
    unfold directSourceFinalVariableIncidenceElementCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id (directSourceFinalVariableIncidenceScaledIdentityBases decider)
      (directSourceFinalVariableIncidenceTagColumn decider)
      (fun symbols => by simp)
      scaledCompiler
      (directSourceFinalVariableIncidenceTagColumnComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceDirectionCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Canonical element codes for final clause-core incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget PeriodicCNF PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- One placeholder per descriptor, including the harmless total fallback
case. -/
def directSourceFinalClauseIncidenceIndexPlaceholders
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun _ : FormulaShapeDirectionOrdering.Token => 0)
    (directSourceFinalClauseDescriptors decider symbols)

/-- Zero-based descriptor positions used as parent clause identities. -/
def directSourceFinalClauseIncidenceIndices
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldRange.values
    (directSourceFinalClauseIncidenceIndexPlaceholders decider symbols)

/-- Internal elements use minor tag zero; the three terminal groups use
top/left/right tags one/two/three. -/
def clauseIncidenceElementTag
    (color : WireColor) (element : X3CClauseElement) : Nat :=
  directSourceFinalClauseElementColorTagBase color +
    match element with
    | .internal _ => 0
    | .terminal terminal =>
        match terminal.group with
        | .top => 1
        | .left => 2
        | .right => 3

/-- Canonical tag of one colored reference in a clause-core triple. -/
def clauseIncidenceReferenceTag
    (set : X3CClauseSet) : WireColor → Nat
  | .red => clauseIncidenceElementTag .red set.coloredReferences.red
  | .green => clauseIncidenceElementTag .green set.coloredReferences.green
  | .blue => clauseIncidenceElementTag .blue set.coloredReferences.blue

/-- Twenty-seven clause-reference tags in the exact triple-major RGB order
of the clause-incidence direction-query block. -/
def finalClauseIncidenceElementTagBlock
    (_ : FormulaShapeDirectionOrdering.Token) : List Nat :=
  allClauseSets.flatMap fun set =>
    [clauseIncidenceReferenceTag set .red,
      clauseIncidenceReferenceTag set .green,
      clauseIncidenceReferenceTag set .blue]

/-- Twenty-seven repeated stride-scaled parent bases per final descriptor. -/
def directSourceFinalClauseIncidenceElementCodeBases
    (indices : List Nat) : List Nat :=
  UnaryFieldFixedCopies.values 27 <|
    UnaryFieldConstantScale.values directSourceFinalElementCodeStride indices

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseIncidenceElementCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete clause-incidence structural-tag column. -/
def directSourceFinalClauseIncidenceElementTags
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldBlockMap.values finalClauseIncidenceElementTagBlock
    (directSourceFinalClauseDescriptors decider symbols)

/-- Complete canonical element codes for final clause-core incidences. -/
def directSourceFinalClauseIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalClauseIncidenceElementCodeBases
      (directSourceFinalClauseIncidenceIndices decider symbols))
    (directSourceFinalClauseIncidenceElementTags decider symbols)

@[simp] theorem finalClauseIncidenceElementTagBlock_length
    (token : FormulaShapeDirectionOrdering.Token) :
    (finalClauseIncidenceElementTagBlock token).length = 27 := by
  simp [finalClauseIncidenceElementTagBlock, allClauseSets]

@[simp] theorem directSourceFinalClauseIncidenceIndexPlaceholders_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceIndexPlaceholders
      decider symbols).length =
      (directSourceFinalClauseDescriptors decider symbols).length := by
  simp [directSourceFinalClauseIncidenceIndexPlaceholders,
    FiniteUnaryFieldMap.values]

@[simp] theorem directSourceFinalClauseIncidenceIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceIndices decider symbols).length =
      (directSourceFinalClauseDescriptors decider symbols).length := by
  simp [directSourceFinalClauseIncidenceIndices, UnaryFieldRange.values]

@[simp] theorem directSourceFinalClauseIncidenceElementCodeBases_length
    (indices : List Nat) :
    (directSourceFinalClauseIncidenceElementCodeBases indices).length =
      27 * indices.length := by
  unfold directSourceFinalClauseIncidenceElementCodeBases
    UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
  rw [List.flatMap_map]
  change (indices.flatMap fun index =>
      List.replicate 27
        (index * directSourceFinalElementCodeStride)).length =
    27 * indices.length
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, List.length_cons]
      rw [induction]
      omega

@[simp] theorem directSourceFinalClauseIncidenceElementTags_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceElementTags decider symbols).length =
      27 * (directSourceFinalClauseDescriptors decider symbols).length := by
  unfold directSourceFinalClauseIncidenceElementTags
    FiniteUnaryFieldBlockMap.values
  induction directSourceFinalClauseDescriptors decider symbols with
  | nil => rfl
  | cons token tokens induction =>
      simp [induction]
      omega

noncomputable def
    directSourceFinalClauseIncidenceIndexPlaceholdersComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIncidenceIndexPlaceholders decider) := by
  unfold directSourceFinalClauseIncidenceIndexPlaceholders
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      fun _ : FormulaShapeDirectionOrdering.Token => 0)

noncomputable def
    directSourceFinalClauseIncidenceIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIncidenceIndices decider) := by
  unfold directSourceFinalClauseIncidenceIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseIncidenceIndexPlaceholdersComputableInPolyTime
      decider)
    UnaryFieldRange.computableInPolyTime

noncomputable def
    directSourceFinalClauseIncidenceElementCodeBasesComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields
      directSourceFinalClauseIncidenceElementCodeBases := by
  unfold directSourceFinalClauseIncidenceElementCodeBases
  exact TM2CompositionMachine.computableInPolyTime
    (UnaryFieldConstantScale.computableInPolyTime
      directSourceFinalElementCodeStride)
    (UnaryFieldFixedCopies.computableInPolyTime 27)

noncomputable def
    directSourceFinalClauseIncidenceElementTagsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIncidenceElementTags decider) := by
  unfold directSourceFinalClauseIncidenceElementTags
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime
      finalClauseIncidenceElementTagBlock)

/-- The complete clause-incidence element-code column compiles in polynomial
time. -/
noncomputable def
    directSourceFinalClauseIncidenceElementCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIncidenceElementCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let baseCompiler := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalClauseIncidenceIndicesComputableInPolyTime decider)
      directSourceFinalClauseIncidenceElementCodeBasesComputableInPolyTime
    unfold directSourceFinalClauseIncidenceElementCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (fun symbols => directSourceFinalClauseIncidenceElementCodeBases
        (directSourceFinalClauseIncidenceIndices decider symbols))
      (directSourceFinalClauseIncidenceElementTags decider)
      (fun symbols => by simp)
      baseCompiler
      (directSourceFinalClauseIncidenceElementTagsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

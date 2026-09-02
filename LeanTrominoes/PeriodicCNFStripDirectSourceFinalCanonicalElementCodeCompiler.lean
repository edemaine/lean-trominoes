/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalVariableElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldFourSlotRankCompiler
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Complete canonical element codes for the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget
open PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- One placeholder for each actual final-clause fan. -/
def directSourceFinalClauseIndexPlaceholderBlock
    (_ : ClauseRibbonFanData) : List Nat := [0]

/-- One dummy unary field per final clause. -/
def directSourceFinalClauseIndexPlaceholders
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldBlockMap.values
    directSourceFinalClauseIndexPlaceholderBlock
    (directSourceFinalClauseFans decider symbols)

/-- Zero-based final clause indices in descriptor order. -/
def directSourceFinalClauseIndices
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldRange.values
    (directSourceFinalClauseIndexPlaceholders decider symbols)

/-- Four repeated stride-scaled bases per final clause. -/
def directSourceFinalClauseElementCodeBases
    (indices : List Nat) : List Nat :=
  UnaryFieldFixedCopies.values 4 <|
    UnaryFieldConstantScale.values directSourceFinalElementCodeStride indices

/-- Disjoint clause-tag blocks for the three colors.  Within each block the
four consecutive tags name the internal, top, left, and right elements. -/
def directSourceFinalClauseElementColorTagBase : WireColor → Nat
  | .red => 16
  | .green => 20
  | .blue => 24

def directSourceFinalClauseElementCodeTags
    (color : WireColor) (indices : List Nat) : List Nat :=
  UnaryFieldConstantOffsets.values
    (directSourceFinalClauseElementColorTagBase color)
    (UnaryFieldFourSlotRanks.values indices)

/-- Canonical clause-internal and terminal structural codes for one color. -/
def directSourceFinalClauseElementCodesFromIndices
    (color : WireColor) (indices : List Nat) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalClauseElementCodeBases indices)
    (directSourceFinalClauseElementCodeTags color indices)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalElementCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Clause element codes for one color, in clause-major
internal/top/left/right order. -/
def directSourceFinalClauseElementCodes
    (color : WireColor) (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalClauseElementCodesFromIndices color
    (directSourceFinalClauseIndices decider symbols)

/-- Complete canonical element-code column for one color. -/
def directSourceFinalOneColorElementCodes
    (color : WireColor) (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCanonicalVariableElementCodes decider color symbols ++
    directSourceFinalClauseElementCodes decider color symbols

/-- Green and blue canonical element-code columns. -/
def directSourceFinalGreenBlueElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalOneColorElementCodes decider .green symbols ++
    directSourceFinalOneColorElementCodes decider .blue symbols

/-- Complete canonical red, green, blue structural-code column. -/
def directSourceFinalCanonicalElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalOneColorElementCodes decider .red symbols ++
    directSourceFinalGreenBlueElementCodes decider symbols

@[simp] theorem directSourceFinalClauseElementCodeBases_length
    (indices : List Nat) :
    (directSourceFinalClauseElementCodeBases indices).length =
      4 * indices.length := by
  unfold directSourceFinalClauseElementCodeBases
    UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
  rw [List.flatMap_map]
  change (indices.flatMap fun index =>
      List.replicate 4
        (index * directSourceFinalElementCodeStride)).length =
    4 * indices.length
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, List.length_cons]
      rw [induction]
      omega

@[simp] theorem directSourceFinalClauseElementCodeTags_length
    (color : WireColor) (indices : List Nat) :
    (directSourceFinalClauseElementCodeTags color indices).length =
      4 * indices.length := by
  simp [directSourceFinalClauseElementCodeTags,
    UnaryFieldConstantOffsets.values, UnaryFieldFourSlotRanks.values,
    Nat.mul_comm]

noncomputable def
    directSourceFinalClauseIndexPlaceholdersComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIndexPlaceholders decider) := by
  unfold directSourceFinalClauseIndexPlaceholders
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFansComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime
      directSourceFinalClauseIndexPlaceholderBlock)

noncomputable def directSourceFinalClauseIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseIndices decider) := by
  unfold directSourceFinalClauseIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseIndexPlaceholdersComputableInPolyTime decider)
    UnaryFieldRange.computableInPolyTime

noncomputable def
    directSourceFinalClauseElementCodesFromIndicesComputableInPolyTime :
    (color : WireColor) →
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseElementCodesFromIndices color) := by
  intro color
  let baseCompiler := TM2CompositionMachine.computableInPolyTime
    (UnaryFieldConstantScale.computableInPolyTime
      directSourceFinalElementCodeStride)
    (UnaryFieldFixedCopies.computableInPolyTime 4)
  let tagCompiler := TM2CompositionMachine.computableInPolyTime
    UnaryFieldFourSlotRanks.computableInPolyTime
    (UnaryFieldConstantOffsets.computableInPolyTime
      (directSourceFinalClauseElementColorTagBase color))
  unfold directSourceFinalClauseElementCodesFromIndices
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields
    directSourceFinalClauseElementCodeBases
    (directSourceFinalClauseElementCodeTags color)
    (fun indices => by simp)
    baseCompiler tagCompiler

noncomputable def directSourceFinalClauseElementCodesComputableInPolyTime
    (color : WireColor) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseElementCodes decider color) := by
  unfold directSourceFinalClauseElementCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseIndicesComputableInPolyTime decider)
    (directSourceFinalClauseElementCodesFromIndicesComputableInPolyTime color)

noncomputable def
    directSourceFinalOneColorElementCodesComputableInPolyTime
    (color : WireColor) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOneColorElementCodes decider color) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOneColorElementCodes
    exact UnaryFieldEncoderMachine.appendComputableInPolyTime
      (directSourceFinalCanonicalVariableElementCodesComputableInPolyTime
        decider color)
      (directSourceFinalClauseElementCodesComputableInPolyTime decider color)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def
    directSourceFinalGreenBlueElementCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGreenBlueElementCodes decider) := by
  unfold directSourceFinalGreenBlueElementCodes
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalOneColorElementCodesComputableInPolyTime
      decider .green)
    (directSourceFinalOneColorElementCodesComputableInPolyTime
      decider .blue)

/-- The complete canonical structural-code column is polynomial-time
computable from the direct source. -/
noncomputable def
    directSourceFinalCanonicalElementCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalElementCodes decider) := by
  unfold directSourceFinalCanonicalElementCodes
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalOneColorElementCodesComputableInPolyTime decider .red)
    (directSourceFinalGreenBlueElementCodesComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

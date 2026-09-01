/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldBooleanFilterCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldThreeSlotRankCompiler

/-! # Canonical variable-element codes for the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- Reserve 32 finite tags beneath every globally unique occurrence key. -/
def directSourceFinalElementCodeStride : Nat := 32

/-- Disjoint finite tag blocks for the red, green, and blue variable-local
elements attached to one active occurrence. -/
def directSourceFinalVariableElementColorTagBase : WireColor → Nat
  | .red => 0
  | .green => 4
  | .blue => 8

/-- Every occurrence contributes its first variable-local element.  The two
additional elements exist exactly for a fixed-red connector. -/
def directSourceFinalVariableElementActiveBlock
    (pair : GroupedVariableFanSlot) : List Bool :=
  match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
  | .fixedRed => [true, true, true]
  | .fixedGreen | .fixedBlue => [true, false, false]

def directSourceFinalVariableElementActiveControls
    (pairs : List GroupedVariableFanSlot) : List Bool :=
  pairs.flatMap directSourceFinalVariableElementActiveBlock

/-- Three repeated stride-scaled bases per active occurrence key. -/
def directSourceFinalVariableElementCandidateBases
    (keys : List Nat) : List Nat :=
  UnaryFieldFixedCopies.values 3 <|
    UnaryFieldConstantScale.values directSourceFinalElementCodeStride keys

/-- Three color-local finite tags per active occurrence key. -/
def directSourceFinalVariableElementCandidateTags
    (color : WireColor) (keys : List Nat) : List Nat :=
  UnaryFieldConstantOffsets.values
    (directSourceFinalVariableElementColorTagBase color)
    (UnaryFieldThreeSlotRanks.values keys)

/-- Three candidate structural codes per occurrence; later filtering removes
the two nonexistent ordinary-module candidates. -/
def directSourceFinalVariableElementCodeCandidates
    (color : WireColor) (keys : List Nat) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalVariableElementCandidateBases keys)
    (directSourceFinalVariableElementCandidateTags color keys)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalVariableElementCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical variable-local element codes for one color. -/
def directSourceFinalCanonicalVariableElementCodes
    (color : WireColor) (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues
    (directSourceFinalVariableElementActiveControls
      (directSourceFinalGroupedVariableFanSlots decider symbols))
    (directSourceFinalVariableElementCodeCandidates color
      (directSourceFinalUniqueFanQueryKeys decider symbols))

@[simp] theorem directSourceFinalVariableElementCandidateBases_length
    (keys : List Nat) :
    (directSourceFinalVariableElementCandidateBases keys).length =
      3 * keys.length := by
  unfold directSourceFinalVariableElementCandidateBases
    UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
  rw [List.flatMap_map]
  change (keys.flatMap fun key =>
      List.replicate 3
        (key * directSourceFinalElementCodeStride)).length =
    3 * keys.length
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, List.length_cons]
      rw [induction]
      omega

@[simp] theorem directSourceFinalVariableElementCandidateTags_length
    (color : WireColor) (keys : List Nat) :
    (directSourceFinalVariableElementCandidateTags color keys).length =
      3 * keys.length := by
  simp [directSourceFinalVariableElementCandidateTags,
    UnaryFieldConstantOffsets.values,
    UnaryFieldThreeSlotRanks.values, Nat.mul_comm]

noncomputable def
    directSourceFinalVariableElementActiveControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      directSourceFinalVariableElementActiveControls :=
  FiniteBlockTransducer.computableInPolyTime
    directSourceFinalVariableElementActiveBlock

noncomputable def
    directSourceFinalVariableElementCodeCandidatesComputableInPolyTime
    (color : WireColor) :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableElementCodeCandidates color) := by
  let baseCompiler := TM2CompositionMachine.computableInPolyTime
    (UnaryFieldConstantScale.computableInPolyTime
      directSourceFinalElementCodeStride)
    (UnaryFieldFixedCopies.computableInPolyTime 3)
  let tagCompiler := TM2CompositionMachine.computableInPolyTime
    UnaryFieldThreeSlotRanks.computableInPolyTime
    (UnaryFieldConstantOffsets.computableInPolyTime
      (directSourceFinalVariableElementColorTagBase color))
  unfold directSourceFinalVariableElementCodeCandidates
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields
    directSourceFinalVariableElementCandidateBases
    (directSourceFinalVariableElementCandidateTags color)
    (fun keys => by simp)
    baseCompiler tagCompiler

/-- The filtered canonical variable-element code column for every fixed color
is polynomial-time computable from the direct source. -/
noncomputable def
    directSourceFinalCanonicalVariableElementCodesComputableInPolyTime
    (color : WireColor) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalVariableElementCodes decider color) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    let controlCompiler := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
      directSourceFinalVariableElementActiveControlsComputableInPolyTime
    let candidateCompiler := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalVariableElementCodeCandidatesComputableInPolyTime
        color)
    unfold directSourceFinalCanonicalVariableElementCodes
    exact UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime
      id
      (fun symbols => directSourceFinalVariableElementActiveControls
        (directSourceFinalGroupedVariableFanSlots decider symbols))
      (fun symbols => directSourceFinalVariableElementCodeCandidates color
        (directSourceFinalUniqueFanQueryKeys decider symbols))
      controlCompiler candidateCompiler
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

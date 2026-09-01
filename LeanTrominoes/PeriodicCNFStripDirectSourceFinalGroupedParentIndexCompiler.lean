/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedParentIndexCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Parent clause indices in grouped variable order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedParentIndexStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Zero-based parent clause index of every final occurrence in the original
clause-major presentation. -/
def directSourceFinalOccurrenceParentIndices
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices
    (directSourceFinalClauseDescriptors decider symbols)

/-- Parent clause indices reordered beside the variable-major active
occurrence stream. -/
def directSourceFinalGroupedParentIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (directSourceFinalOccurrenceParentIndices decider symbols)

@[simp] theorem directSourceFinalOccurrenceParentIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceParentIndices decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceParentIndices
  rw [HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_length,
    directSourceFinalClauseDescriptors_occurrenceData_eq]

@[simp] theorem directSourceFinalGroupedParentIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedParentIndices decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedParentIndices
  rw [UnaryIndexedValueLookup.values_length,
    directSourceFinalGroupedOccurrenceIndices_length]

noncomputable def
    directSourceFinalOccurrenceParentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceParentIndices decider) := by
  unfold directSourceFinalOccurrenceParentIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndicesComputableInPolyTime

/-- Grouped parent-clause indices are polynomial-time computable from the
direct source. -/
noncomputable def
    directSourceFinalGroupedParentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedParentIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedParentIndices
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalGroupedOccurrenceIndices decider)
      (directSourceFinalOccurrenceParentIndices decider)
      (directSourceFinalGroupedOccurrenceIndicesComputableInPolyTime decider)
      (directSourceFinalOccurrenceParentIndicesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

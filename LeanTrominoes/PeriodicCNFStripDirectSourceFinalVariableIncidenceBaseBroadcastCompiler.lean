/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementSelectorCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Dynamic identity columns broadcast over variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

/-- Number of RGB incidence selectors emitted by one grouped active
occurrence. -/
def groupedVariableIncidenceElementBlockLength
    (pair : GroupedVariableFanSlot) : Nat :=
  (groupedVariableIncidenceElementSelectorBlock pair).length

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalVariableIncidenceBroadcastStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Zero-based grouped-occurrence indices repeated over every incidence in
that occurrence's finite selector block. -/
def directSourceFinalVariableIncidenceBlockIndices
    (symbols : List encoding.Γ) : List Nat :=
  FiniteBlockIndices.indices groupedVariableIncidenceElementBlockLength
    (directSourceFinalGroupedVariableFanSlots decider symbols)

/-- Current occurrence keys repeated over their complete incidence blocks. -/
def directSourceFinalVariableIncidenceCurrentKeys
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalVariableIncidenceBlockIndices decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)

/-- Cyclic-successor occurrence keys repeated over the current occurrence's
complete incidence block. -/
def directSourceFinalVariableIncidenceNextKeys
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalVariableIncidenceBlockIndices decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)

/-- Parent clause indices repeated over every incidence in the corresponding
variable occurrence. -/
def directSourceFinalVariableIncidenceParentIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalVariableIncidenceBlockIndices decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)

/-- The common finite block-index column compiles in polynomial time. -/
noncomputable def
    directSourceFinalVariableIncidenceBlockIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceBlockIndices decider) := by
  unfold directSourceFinalVariableIncidenceBlockIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (FiniteBlockIndices.indicesComputableInPolyTime
      groupedVariableIncidenceElementBlockLength)

/-- Reuse the compiled block-index column to broadcast any compiled unary
value column aligned with the grouped occurrences. -/
private noncomputable def
    directSourceFinalVariableIncidenceBroadcastComputableInPolyTime
    (candidateValues : List encoding.Γ → List Nat)
    (candidateCompiler :
      TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        candidateValues) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => UnaryIndexedValueLookup.values
        (directSourceFinalVariableIncidenceBlockIndices decider symbols)
        (candidateValues symbols)) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime
      id (directSourceFinalVariableIncidenceBlockIndices decider)
      candidateValues
      (directSourceFinalVariableIncidenceBlockIndicesComputableInPolyTime
        decider)
      candidateCompiler
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def
    directSourceFinalVariableIncidenceCurrentKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceCurrentKeys decider) := by
  exact directSourceFinalVariableIncidenceBroadcastComputableInPolyTime
    decider (directSourceFinalUniqueFanQueryKeys decider)
    (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)

noncomputable def
    directSourceFinalVariableIncidenceNextKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceNextKeys decider) := by
  exact directSourceFinalVariableIncidenceBroadcastComputableInPolyTime
    decider (directSourceFinalGroupedNextOccurrenceKeys decider)
    (directSourceFinalGroupedNextOccurrenceKeysComputableInPolyTime decider)

noncomputable def
    directSourceFinalVariableIncidenceParentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableIncidenceParentIndices decider) := by
  exact directSourceFinalVariableIncidenceBroadcastComputableInPolyTime
    decider (directSourceFinalGroupedParentIndices decider)
    (directSourceFinalGroupedParentIndicesComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

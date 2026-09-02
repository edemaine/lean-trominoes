/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceParentPermutation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSelectorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceExpectedBlockComponents

/-! # Parent-terminal codes attached to grouped occurrence records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM

/-- The three RGB clause-terminal element codes selected by one connector
kind at a given actual final-clause position. -/
def finalConnectorParentElementCodeBlock
    (kind : VariableConnectorKind) (parent : Nat) : List Nat :=
  [parent * directSourceFinalElementCodeStride +
      (variableIncidenceClauseTerminalTag kind .red).val,
    parent * directSourceFinalElementCodeStride +
      (variableIncidenceClauseTerminalTag kind .green).val,
    parent * directSourceFinalElementCodeStride +
      (variableIncidenceClauseTerminalTag kind .blue).val]

/-- The three clause-terminal element codes referenced by one finite final
occurrence record. -/
def finalOccurrenceParentElementCodeBlock
    (data : FinalFanOccurrenceData) (parent : Nat) : List Nat :=
  finalConnectorParentElementCodeBlock data.kind parent

/-- Once the grouped fan/slot kind is identified with its grouped occurrence
record, the audited parent selector block is exactly the occurrence-based RGB
terminal block. -/
theorem groupedVariableIncidenceExpectedParentElementCodeBlock_eq_of_kind_eq
    (pair : GroupedVariableFanSlot) (data : FinalFanOccurrenceData)
    (current next parent : Nat)
    (kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) = data.kind) :
    groupedVariableIncidenceExpectedParentElementCodeBlock
        pair current next parent =
      finalOccurrenceParentElementCodeBlock data parent := by
  simp [groupedVariableIncidenceExpectedParentElementCodeBlock,
    VariableIncidenceLocalControl.expectedParentSelectors,
    VariableIncidenceLocalControl.ofPair,
    VariableIncidenceLocalControl.slot,
    VariableIncidenceLocalControl.parent,
    finalOccurrenceParentElementCodeBlock,
    finalConnectorParentElementCodeBlock,
    kindEq]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalGroupedOccurrenceParentElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith finalOccurrenceParentElementCodeBlock
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)).flatten

def directSourceFinalOccurrenceParentElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith finalOccurrenceParentElementCodeBlock
    (directSourceFinalCompiledOccurrenceData decider symbols)
    (directSourceFinalOccurrenceParentIndices decider symbols)).flatten

/-- Stable-key regrouping preserves the complete RGB parent-terminal code
stream as a multiset. -/
theorem directSourceFinalGroupedOccurrenceParentElementCodes_perm
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceParentElementCodes
        decider symbols).Perm
      (directSourceFinalOccurrenceParentElementCodes decider symbols) := by
  unfold directSourceFinalGroupedOccurrenceParentElementCodes
    directSourceFinalOccurrenceParentElementCodes
  have attached := directSourceFinalGroupedOccurrenceParents_perm
    decider symbols
  rw [List.zipWith_flatten_eq_pair_flatMap,
    List.zipWith_flatten_eq_pair_flatMap]
  exact attached.flatMap fun pair _ =>
    List.Perm.refl
      (finalOccurrenceParentElementCodeBlock pair.1 pair.2)

end LeanTrominoes.PeriodicCNFStripReduction

end

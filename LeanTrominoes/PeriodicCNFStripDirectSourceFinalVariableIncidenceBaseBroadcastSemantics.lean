/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceBaseBroadcastCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementSelectorSemantics
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Semantics of variable-incidence identity broadcasts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- Each local triple contributes exactly its three RGB selectors. -/
@[simp] theorem groupedVariableIncidenceElementBlockLength_eq
    (pair : GroupedVariableFanSlot) :
    groupedVariableIncidenceElementBlockLength pair =
      3 * (groupedVariableIncidenceTriples pair).length := by
  unfold groupedVariableIncidenceElementBlockLength
  rw [groupedVariableIncidenceElementSelectorBlock_length,
    groupedVariableIncidencePrefixQueryBlock_length]

/-- Every grouped occurrence emits a nonempty incidence block. -/
theorem groupedVariableIncidenceElementBlockLength_pos
    (pair : GroupedVariableFanSlot) :
    0 < groupedVariableIncidenceElementBlockLength pair := by
  unfold groupedVariableIncidenceElementBlockLength
  rw [groupedVariableIncidenceElementSelectorBlock_length,
    groupedVariableIncidencePrefixQueryBlock_length]
  rw [groupedVariableIncidenceTriples_length]
  cases pair.1.kind (groupedVariableFanSiteSlot pair.2) <;> simp

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem directSourceFinalVariableIncidenceBroadcast_eq
    (symbols : List encoding.Γ) (candidateValues : List Nat)
    (lengthEq :
      (directSourceFinalGroupedVariableFanSlots decider symbols).length =
        candidateValues.length) :
    UnaryIndexedValueLookup.values
        (directSourceFinalVariableIncidenceBlockIndices decider symbols)
        candidateValues =
      FiniteBlockIndices.broadcastValues
        groupedVariableIncidenceElementBlockLength
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        candidateValues := by
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt]
  · unfold directSourceFinalVariableIncidenceBlockIndices
    rw [FiniteBlockIndices.indices_eq_expected]
    exact FiniteBlockIndices.expected_lookup_eq_broadcastValues
      groupedVariableIncidenceElementBlockLength
      (directSourceFinalGroupedVariableFanSlots decider symbols)
      candidateValues 0 lengthEq
      (fun pair _ => groupedVariableIncidenceElementBlockLength_pos pair)
  · intro query queryMember
    have bound := FiniteBlockIndices.mem_indices_lt_length
      groupedVariableIncidenceElementBlockLength
      (directSourceFinalGroupedVariableFanSlots decider symbols)
      query queryMember
    omega

/-- The current occurrence key is repeated over exactly its finite incidence
block. -/
theorem directSourceFinalVariableIncidenceCurrentKeys_eq_broadcastValues
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceCurrentKeys decider symbols =
      FiniteBlockIndices.broadcastValues
        groupedVariableIncidenceElementBlockLength
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols) := by
  unfold directSourceFinalVariableIncidenceCurrentKeys
  apply directSourceFinalVariableIncidenceBroadcast_eq decider
  exact directSourceFinalGroupedVariableFanSlots_length decider symbols

/-- The cyclic-successor occurrence key is repeated over the same blocks. -/
theorem directSourceFinalVariableIncidenceNextKeys_eq_broadcastValues
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceNextKeys decider symbols =
      FiniteBlockIndices.broadcastValues
        groupedVariableIncidenceElementBlockLength
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalGroupedNextOccurrenceKeys decider symbols) := by
  unfold directSourceFinalVariableIncidenceNextKeys
  apply directSourceFinalVariableIncidenceBroadcast_eq decider
  rw [directSourceFinalGroupedVariableFanSlots_length,
    directSourceFinalGroupedNextOccurrenceKeys_length]

/-- The parent clause index is repeated over the same blocks. -/
theorem directSourceFinalVariableIncidenceParentIndices_eq_broadcastValues
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceParentIndices decider symbols =
      FiniteBlockIndices.broadcastValues
        groupedVariableIncidenceElementBlockLength
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalGroupedParentIndices decider symbols) := by
  unfold directSourceFinalVariableIncidenceParentIndices
  apply directSourceFinalVariableIncidenceBroadcast_eq decider
  rw [directSourceFinalGroupedVariableFanSlots_length,
    directSourceFinalGroupedParentIndices_length]

@[simp] theorem directSourceFinalVariableIncidenceBlockIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceBlockIndices decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  unfold directSourceFinalVariableIncidenceBlockIndices
    directSourceFinalVariableIncidenceElementSelectors
  rw [FiniteBlockIndices.indices_length, List.length_flatMap]
  rfl

@[simp] theorem directSourceFinalVariableIncidenceCurrentKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceCurrentKeys decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceCurrentKeys]

@[simp] theorem directSourceFinalVariableIncidenceNextKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceNextKeys decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceNextKeys]

@[simp] theorem directSourceFinalVariableIncidenceParentIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceParentIndices decider symbols).length =
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceParentIndices]

end LeanTrominoes.PeriodicCNFStripReduction

end

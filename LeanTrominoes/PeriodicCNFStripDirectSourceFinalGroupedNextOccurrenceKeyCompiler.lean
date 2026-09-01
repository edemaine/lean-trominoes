/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Cyclic successor occurrence keys in grouped variable order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM

/-- Forward cyclic rank determined entirely by a grouped fan's active slot
and positive active-occurrence count. -/
def groupedVariableNextOccurrenceRank
    (pair : GroupedVariableFanSlot) : Nat :=
  ((groupedVariableFanSiteSlot pair.2).index + 1) % pair.1.count

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalNextOccurrenceKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The clause-major atom-identity bases reordered beside grouped active
occurrences. -/
def directSourceFinalGroupedScaledAtomIdentityCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (directSourceFinalScaledAtomIdentityCodes decider symbols)

/-- One finite successor rank per grouped active occurrence. -/
def directSourceFinalGroupedNextOccurrenceRanks
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values groupedVariableNextOccurrenceRank
    (directSourceFinalGroupedVariableFanSlots decider symbols)

/-- Base-three key of every cyclic successor occurrence, in the same
variable-major order as the grouped incidence blocks. -/
def directSourceFinalGroupedNextOccurrenceKeys
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalGroupedScaledAtomIdentityCodes decider symbols)
    (directSourceFinalGroupedNextOccurrenceRanks decider symbols)

@[simp] theorem directSourceFinalGroupedScaledAtomIdentityCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedScaledAtomIdentityCodes decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedScaledAtomIdentityCodes
  rw [UnaryIndexedValueLookup.values_length,
    directSourceFinalGroupedOccurrenceIndices_length]

@[simp] theorem directSourceFinalGroupedNextOccurrenceRanks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedNextOccurrenceRanks decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedNextOccurrenceRanks
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalGroupedVariableFanSlots_length]

@[simp] theorem directSourceFinalGroupedNextOccurrenceKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedNextOccurrenceKeys
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalGroupedScaledAtomIdentityCodes_length,
    directSourceFinalGroupedNextOccurrenceRanks_length, min_self]

noncomputable def
    directSourceFinalGroupedScaledAtomIdentityCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedScaledAtomIdentityCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedScaledAtomIdentityCodes
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalGroupedOccurrenceIndices decider)
      (directSourceFinalScaledAtomIdentityCodes decider)
      (directSourceFinalGroupedOccurrenceIndicesComputableInPolyTime decider)
      (directSourceFinalScaledAtomIdentityCodesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def
    directSourceFinalGroupedNextOccurrenceRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedNextOccurrenceRanks decider) := by
  unfold directSourceFinalGroupedNextOccurrenceRanks
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      groupedVariableNextOccurrenceRank)

/-- Grouped cyclic successor keys are polynomial-time computable from the
direct source without a dynamic list rotation. -/
noncomputable def
    directSourceFinalGroupedNextOccurrenceKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedNextOccurrenceKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedNextOccurrenceKeys
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalGroupedScaledAtomIdentityCodes decider)
      (directSourceFinalGroupedNextOccurrenceRanks decider)
      (fun symbols => by
        rw [directSourceFinalGroupedScaledAtomIdentityCodes_length,
          directSourceFinalGroupedNextOccurrenceRanks_length])
      (directSourceFinalGroupedScaledAtomIdentityCodesComputableInPolyTime
        decider)
      (directSourceFinalGroupedNextOccurrenceRanksComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedAtomIdentityBroadcast
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeLocalBound
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeSemantics

/-! # Blockwise semantics of inherited implication-cycle ring codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open HorizontalRoutedRouteHeaderInheritedSourceSelection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Presentation-relative scope controls for one fixed nine-clause
implication cycle. -/
def directSourceFinalLocalCyclePresentationAtomScopeControls :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  HorizontalRoutedRouteHeaderPresentationAtomScope.output
    FormulaShapeFixedEightDirection.cycleClauseDescriptors

/-- One copy of the fixed local scope table per distinct retained-source
identity. -/
def directSourceFinalCyclePresentationAtomScopeControls
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  (directSourceFinalDistinctAtomIdentityIndices decider symbols).flatMap
    fun _ => directSourceFinalLocalCyclePresentationAtomScopeControls

private theorem directSourceFinalCycleOccurrenceBlockLength_variable_eq_slots :
    directSourceFinalCycleOccurrenceBlockLength
        FormulaShapeDirectionOrdering.Token.variable =
      (directSourceFinalLocalCycleRingVertexSlots.map Fin.val).length := by
  rw [List.length_map]
  simpa [directSourceFinalCycleOccurrenceBlockLength,
    directSourceFinalCycleClauseDescriptorBlock,
    FormulaShapeFixedEightDirection.cycleClauseBlock] using
      directSourceFinalLocalCycleRingVertexSlots_length.symm

@[simp] theorem directSourceFinalLocalCyclePresentationAtomScopeControls_length :
    directSourceFinalLocalCyclePresentationAtomScopeControls.length =
      (directSourceFinalLocalCycleRingVertexSlots.map Fin.val).length := by
  unfold directSourceFinalLocalCyclePresentationAtomScopeControls
  rw [HorizontalRoutedRouteHeaderPresentationAtomScope.output_length,
    List.length_map,
    directSourceFinalLocalCycleRingVertexSlots_length]

/-- The compiled numeric cycle-slot column is the same fixed local table
repeated once for each distinct retained-source identity. -/
theorem directSourceFinalCycleRingVertexSlotValues_eq_flatMap
    (symbols : List encoding.Γ) :
    directSourceFinalCycleRingVertexSlotValues decider symbols =
      (directSourceFinalDistinctAtomIdentityIndices decider symbols).flatMap
        fun _ => directSourceFinalLocalCycleRingVertexSlots.map Fin.val := by
  unfold directSourceFinalCycleRingVertexSlotValues
    directSourceFinalCycleRingVertexSlots
  rw [directRetainedFigureNineFiniteSourceVariableMarkers_eq_replicate_identities,
    List.map_flatMap]
  induction directSourceFinalDistinctAtomIdentityIndices decider symbols with
  | nil => rfl
  | cons identity identities induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.flatMap_cons]
      change (directSourceFinalLocalCycleRingVertexSlots.map Fin.val ++ _) = _
      rw [induction]

private theorem zipWith_repeated_cycle_blocks
    (identities slots : List Nat) :
    List.zipWith inheritedRingAtomCode
        (identities.flatMap fun identity =>
          List.replicate slots.length identity)
        (identities.flatMap fun _ => slots) =
      identities.flatMap fun identity =>
        slots.map (inheritedRingAtomCode identity) := by
  have blockZip (identity : Nat) :
      List.zipWith inheritedRingAtomCode
          (List.replicate slots.length identity) slots =
        slots.map (inheritedRingAtomCode identity) := by
    induction slots with
    | nil => rfl
    | cons slot slots induction =>
        simp [List.replicate_succ, induction]
  induction identities with
  | nil => rfl
  | cons identity identities induction =>
      simp only [List.flatMap_cons]
      rw [List.zipWith_append (by simp), blockZip, induction]

/-- Before inherited-position selection, the complete cycle code column is a
flat map of one base-nine local ring table per distinct source identity. -/
theorem directSourceFinalCycleInheritedRingAtomCodes_eq_flatMap
    (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedRingAtomCodes decider symbols =
      (directSourceFinalDistinctAtomIdentityIndices decider symbols).flatMap
        fun identity =>
          (directSourceFinalLocalCycleRingVertexSlots.map Fin.val).map
            (inheritedRingAtomCode identity) := by
  rw [directSourceFinalCycleInheritedRingAtomCodes_eq_zipWith,
    directSourceFinalCycleInheritedAtomIdentityIndices_eq_flatMap_replicate,
    directSourceFinalCycleRingVertexSlotValues_eq_flatMap,
    directSourceFinalCycleOccurrenceBlockLength_variable_eq_slots]
  exact zipWith_repeated_cycle_blocks _ _

/-- Selecting inherited cycle positions distributes across retained-source
identity blocks and leaves the fixed twice-per-slot local table. -/
theorem directSourceFinalCycleSelectedInheritedRingAtomCodes_eq_flatMap
    (symbols : List encoding.Γ) :
    selectedInheritedValues
        (directSourceFinalCyclePresentationAtomScopeControls decider symbols)
        (directSourceFinalCycleInheritedRingAtomCodes decider symbols) =
      (directSourceFinalDistinctAtomIdentityIndices decider symbols).flatMap
        fun identity =>
          directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
            (inheritedRingAtomCode identity) := by
  rw [directSourceFinalCycleInheritedRingAtomCodes_eq_flatMap]
  unfold directSourceFinalCyclePresentationAtomScopeControls
  rw [selectedInheritedValues_flatMap]
  · apply List.flatMap_congr
    intro identity _
    rw [selectedInheritedValues_map]
    rfl
  · intro identity _
    simp only [List.length_map]
    unfold directSourceFinalLocalCyclePresentationAtomScopeControls
    rw [HorizontalRoutedRouteHeaderPresentationAtomScope.output_length]
    exact directSourceFinalLocalCycleRingVertexSlots_length.symm

end LeanTrominoes.PeriodicCNFStripReduction

end

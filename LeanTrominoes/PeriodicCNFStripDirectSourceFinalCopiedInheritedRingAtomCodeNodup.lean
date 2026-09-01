/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedPresentationAtomScopeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPreFigureNineInheritedRingAtomCodeNodup
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderInheritedSourceSelectionSemantics

/-! # Duplicate-free selected copied inherited ring codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

set_option maxHeartbeats 800000

open HorizontalRoutedRouteHeaderCopiedSourcePosition
open HorizontalRoutedRouteHeaderInheritedSourceSelection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Pointwise zipping two maps of the same source list is map of the
pointwise combination. -/
private theorem zipWith_map_map
    {Value First Second Output : Type*}
    (values : List Value) (first : Value → First)
    (second : Value → Second) (combine : First → Second → Output) :
    List.zipWith combine (values.map first) (values.map second) =
      values.map fun value => combine (first value) (second value) := by
  induction values with
  | nil => rfl
  | cons value values induction => simp [induction]

/-- An in-range lookup in a zip is the pointwise combination of lookups in
the two equally long source lists. -/
private theorem zipWith_getD
    {First Second Output : Type*}
    (combine : First → Second → Output)
    (first : List First) (second : List Second)
    (firstDefault : First) (secondDefault : Second)
    (index : Nat) (indexLt : index < first.length)
    (lengthEq : first.length = second.length) :
    (List.zipWith combine first second).getD index
        (combine firstDefault secondDefault) =
      combine (first.getD index firstDefault)
        (second.getD index secondDefault) := by
  have secondLt : index < second.length := by omega
  have zippedLt : index < (List.zipWith combine first second).length := by
    simp only [List.length_zipWith]
    omega
  rw [List.getD_eq_getElem _ _ zippedLt,
    List.getD_eq_getElem _ _ indexLt,
    List.getD_eq_getElem _ _ secondLt,
    List.getElem_zipWith]

/-- The common copied source-position selection commutes with base-nine
pointwise pairing of equally long identity and slot columns. -/
private theorem selectedValues_zipWith_inheritedRingAtomCode
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (identities slots : List Nat)
    (identitiesLength : identities.length = totalSourceWordCount source)
    (slotsLength : slots.length = totalSourceWordCount source) :
    selectedValues source
        (List.zipWith inheritedRingAtomCode identities slots) =
      List.zipWith inheritedRingAtomCode
        (selectedValues source identities)
        (selectedValues source slots) := by
  have zippedLength :
      (List.zipWith inheritedRingAtomCode identities slots).length =
        totalSourceWordCount source := by
    simp only [List.length_zipWith, identitiesLength, slotsLength,
      Nat.min_self]
  rw [selectedValues_eq_map_getD _ _ zippedLength,
    selectedValues_eq_map_getD _ _ identitiesLength,
    selectedValues_eq_map_getD _ _ slotsLength,
    zipWith_map_map]
  apply List.map_congr_left
  intro position positionMember
  have positionLt : position < identities.length := by
    have bounded := (List.forall_iff_forall_mem.mp
      (positions_forall_lt source)) position positionMember
    omega
  simpa [inheritedRingAtomCode] using
    zipWith_getD inheritedRingAtomCode identities slots 0 0
      position positionLt (identitiesLength.trans slotsLength.symm)

/-- The compiled copied inherited ring-code list is selection of the single
aligned pre-Figure9 candidate-code column. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_selectedValues
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      selectedValues
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
        (directSourceFinalPreFigureNineInheritedRingAtomCodes
          decider symbols) := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_zipWith,
    directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_zipWith]
  unfold directSourceFinalCopiedInheritedAtomIdentityIndices
    directSourceFinalCopiedTerminalSlotValues
  symm
  exact selectedValues_zipWith_inheritedRingAtomCode
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols)
    (directSourceFinalTerminalSlotValues decider symbols)
    (directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_total
      decider symbols)
    (directSourceFinalTerminalSlotValues_length_eq_total decider symbols)

/-- Discarding parent-local outputs from the actual copied inherited-code
column leaves a duplicate-free list. -/
theorem directSourceFinalCopiedSelectedInheritedRingAtomCodes_nodup
    (symbols : List encoding.Γ) :
    (selectedInheritedValues
      (directSourceFinalCopiedPresentationAtomScopeControls decider symbols)
      (directSourceFinalCopiedInheritedRingAtomCodes
        decider symbols)).Nodup := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_selectedValues]
  unfold directSourceFinalCopiedPresentationAtomScopeControls
  exact selectedInheritedValues_selectedValues_nodup
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalPreFigureNineInheritedRingAtomCodes decider symbols)
    (directSourceFinalPreFigureNineInheritedRingAtomCodes_length_eq_total
      decider symbols)
    (directSourceFinalPreFigureNineInheritedRingAtomCodes_nodup
      decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end

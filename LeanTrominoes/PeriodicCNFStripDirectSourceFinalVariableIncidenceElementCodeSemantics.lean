/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryBooleanChoiceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementSelectorSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of final variable-incidence element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

private theorem nextControlColumn_getD
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) (index : Nat) :
    (directSourceFinalVariableIncidenceNextControlColumn
      decider symbols).getD index false =
      VariableIncidenceElementSelector.usesNext
        ((directSourceFinalVariableIncidenceElementSelectors
          decider symbols).getD index default) := by
  unfold directSourceFinalVariableIncidenceNextControlColumn
  rw [directSourceFinalVariableIncidenceNextControls_eq_map]
  simpa [VariableIncidenceElementSelector.usesNext] using
    (List.getD_map
      (l := directSourceFinalVariableIncidenceElementSelectors
        decider symbols)
      (d := (default : VariableIncidenceElementSelector))
      (n := index) VariableIncidenceElementSelector.usesNext)

private theorem parentControlColumn_getD
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) (index : Nat) :
    (directSourceFinalVariableIncidenceParentControlColumn
      decider symbols).getD index false =
      VariableIncidenceElementSelector.usesParent
        ((directSourceFinalVariableIncidenceElementSelectors
          decider symbols).getD index default) := by
  unfold directSourceFinalVariableIncidenceParentControlColumn
  rw [directSourceFinalVariableIncidenceParentControls_eq_map]
  simpa [VariableIncidenceElementSelector.usesParent] using
    (List.getD_map
      (l := directSourceFinalVariableIncidenceElementSelectors
        decider symbols)
      (d := (default : VariableIncidenceElementSelector))
      (n := index) VariableIncidenceElementSelector.usesParent)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- At every aligned incidence, the first finite control chooses precisely
between the current and cyclic-successor occurrence keys. -/
theorem directSourceFinalVariableIncidenceSelectedOccurrenceKeys_getD
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length) :
    (directSourceFinalVariableIncidenceSelectedOccurrenceKeys
      decider symbols).getD index 0 =
      if VariableIncidenceElementSelector.usesNext
          ((directSourceFinalVariableIncidenceElementSelectors
            decider symbols).getD index default) then
        (directSourceFinalVariableIncidenceNextKeys
          decider symbols).getD index 0
      else
        (directSourceFinalVariableIncidenceCurrentKeys
          decider symbols).getD index 0 := by
  unfold directSourceFinalVariableIncidenceSelectedOccurrenceKeys
  rw [AlignedUnaryBooleanChoice.selectedValues_getD
    (controlsFirst := by
      rw [directSourceFinalVariableIncidenceNextControlColumn_length,
        directSourceFinalVariableIncidenceCurrentKeys_length])
    (firstSecond := by
      rw [directSourceFinalVariableIncidenceCurrentKeys_length,
        directSourceFinalVariableIncidenceNextKeys_length])
    (indexLt := by
      simpa using indexLt),
    nextControlColumn_getD]

/-- The second finite control switches the selected occurrence identity to
the parent-clause index exactly for terminal connector incidences. -/
theorem directSourceFinalVariableIncidenceSelectedIdentityBases_getD
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directSourceFinalVariableIncidenceElementSelectors
        decider symbols).length) :
    (directSourceFinalVariableIncidenceSelectedIdentityBases
      decider symbols).getD index 0 =
      if VariableIncidenceElementSelector.usesParent
          ((directSourceFinalVariableIncidenceElementSelectors
            decider symbols).getD index default) then
        (directSourceFinalVariableIncidenceParentIndices
          decider symbols).getD index 0
      else if VariableIncidenceElementSelector.usesNext
          ((directSourceFinalVariableIncidenceElementSelectors
            decider symbols).getD index default) then
        (directSourceFinalVariableIncidenceNextKeys
          decider symbols).getD index 0
      else
        (directSourceFinalVariableIncidenceCurrentKeys
          decider symbols).getD index 0 := by
  unfold directSourceFinalVariableIncidenceSelectedIdentityBases
  rw [AlignedUnaryBooleanChoice.selectedValues_getD
    (controlsFirst := by
      rw [directSourceFinalVariableIncidenceParentControlColumn_length,
        directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length])
    (firstSecond := by
      rw [directSourceFinalVariableIncidenceSelectedOccurrenceKeys_length,
        directSourceFinalVariableIncidenceParentIndices_length])
    (indexLt := by
      simpa using indexLt),
    parentControlColumn_getD,
    directSourceFinalVariableIncidenceSelectedOccurrenceKeys_getD
      decider symbols index indexLt]

/-- Aligned addition appends each finite structural tag to its stride-scaled
selected identity base. -/
theorem directSourceFinalVariableIncidenceElementCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceElementCodes decider symbols =
      List.zipWith (fun base tag => base + tag)
        (directSourceFinalVariableIncidenceScaledIdentityBases
          decider symbols)
        (directSourceFinalVariableIncidenceTagColumn decider symbols) := by
  unfold directSourceFinalVariableIncidenceElementCodes
    AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [directSourceFinalVariableIncidenceScaledIdentityBases_length,
      directSourceFinalVariableIncidenceTagColumn_length])

/-- The compiled code column has exactly one entry per grouped variable
incidence query. -/
@[simp] theorem directSourceFinalVariableIncidenceElementCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceElementCodes decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  rw [directSourceFinalVariableIncidenceElementCodes_eq_zipWith,
    List.length_zipWith,
    directSourceFinalVariableIncidenceScaledIdentityBases_length,
    directSourceFinalVariableIncidenceTagColumn_length, min_self,
    directSourceFinalVariableIncidenceElementSelectors_length]

end LeanTrominoes.PeriodicCNFStripReduction

end

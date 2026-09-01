/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForallTwoPermFlatten
import LeanTrominoes.ListZipWithFourForallTwo
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotActive
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeOccurrenceBlockSemantics

/-! # Expected occurrence blocks of variable-incidence element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Exact audited element-code multiset of one active grouped occurrence. -/
def groupedVariableIncidenceExpectedElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  (VariableIncidenceLocalControl.ofPair pair).expectedSelectors.map
    fun selector =>
      variableIncidenceElementCode selector current next parent

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Replacing every compiled variable-incidence block by its audited local
multiset preserves the complete incidence-code multiset. -/
theorem directSourceFinalVariableIncidenceElementCodes_perm_expectedBlocks
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceElementCodes decider symbols).Perm
      (List.zipWith4 groupedVariableIncidenceExpectedElementCodeBlock
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols)
        (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
        (directSourceFinalGroupedParentIndices decider symbols)).flatten := by
  rw [directSourceFinalVariableIncidenceElementCodes_eq_occurrenceBlocks]
  apply List.Forall₂.flatten_perm
  apply List.zipWith4_forall₂ List.Perm
  intro pair pairMember current next parent
  exact groupedVariableIncidenceElementCodeBlock_perm_expected
    pair current next parent
    (directSourceFinalGroupedVariableFanSlots_active
      decider symbols pair pairMember)

end LeanTrominoes.PeriodicCNFStripReduction

end

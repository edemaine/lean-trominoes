/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourFlattenAppendPerm
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceExpectedBlockSemantics

/-! # Variable-local and parent components of expected incidence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

def groupedVariableIncidenceExpectedCycleElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  (VariableIncidenceLocalControl.ofPair pair).expectedCycleSelectors.map
    fun selector =>
      variableIncidenceElementCode selector current next parent

def groupedVariableIncidenceExpectedPrivateElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  (VariableIncidenceLocalControl.ofPair pair).expectedPrivateSelectors.map
    fun selector =>
      variableIncidenceElementCode selector current next parent

def groupedVariableIncidenceExpectedVariableElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  groupedVariableIncidenceExpectedCycleElementCodeBlock
      pair current next parent ++
    groupedVariableIncidenceExpectedPrivateElementCodeBlock
      pair current next parent

def groupedVariableIncidenceExpectedParentElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  (VariableIncidenceLocalControl.ofPair pair).expectedParentSelectors.map
    fun selector =>
      variableIncidenceElementCode selector current next parent

theorem groupedVariableIncidenceExpectedElementCodeBlock_eq_components
    (pair : GroupedVariableFanSlot) (current next parent : Nat) :
    groupedVariableIncidenceExpectedElementCodeBlock
        pair current next parent =
      groupedVariableIncidenceExpectedVariableElementCodeBlock
          pair current next parent ++
        groupedVariableIncidenceExpectedParentElementCodeBlock
          pair current next parent := by
  simp [groupedVariableIncidenceExpectedElementCodeBlock,
    groupedVariableIncidenceExpectedVariableElementCodeBlock,
    groupedVariableIncidenceExpectedCycleElementCodeBlock,
    groupedVariableIncidenceExpectedPrivateElementCodeBlock,
    groupedVariableIncidenceExpectedParentElementCodeBlock,
    VariableIncidenceLocalControl.expectedSelectors]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalExpectedVariableIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith4
    groupedVariableIncidenceExpectedVariableElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)).flatten

def directSourceFinalExpectedParentIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith4
    groupedVariableIncidenceExpectedParentElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)).flatten

/-- All locally audited variable-incidence codes can be reordered into the
variable-local contribution followed by the parent-clause contribution. -/
theorem directSourceFinalVariableIncidenceElementCodes_perm_components
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceElementCodes decider symbols).Perm
      (directSourceFinalExpectedVariableIncidenceElementCodes
          decider symbols ++
        directSourceFinalExpectedParentIncidenceElementCodes
          decider symbols) := by
  apply (directSourceFinalVariableIncidenceElementCodes_perm_expectedBlocks
    decider symbols).trans
  have blockEq :
      groupedVariableIncidenceExpectedElementCodeBlock =
        fun pair current next parent =>
          groupedVariableIncidenceExpectedVariableElementCodeBlock
              pair current next parent ++
            groupedVariableIncidenceExpectedParentElementCodeBlock
              pair current next parent := by
    funext pair current next parent
    exact groupedVariableIncidenceExpectedElementCodeBlock_eq_components
      pair current next parent
  rw [blockEq]
  exact List.zipWith4_flatten_append_perm
    groupedVariableIncidenceExpectedVariableElementCodeBlock
    groupedVariableIncidenceExpectedParentElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end

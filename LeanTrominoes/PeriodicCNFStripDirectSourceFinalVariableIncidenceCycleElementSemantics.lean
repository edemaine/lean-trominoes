/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourProjection
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceCycleSecondKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSelectorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceExpectedBlockComponents

/-! # Cycle-element multiplicities in variable-incidence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- The canonical red cycle-element code at an occurrence key. -/
def variableIncidenceCycleElementCode (key : Nat) : Nat :=
  key * directSourceFinalElementCodeStride

/-- The two audited cycle references of one occurrence use its current key
and the locally selected second cycle key. -/
theorem groupedVariableIncidenceExpectedCycleElementCodeBlock_eq
    (pair : GroupedVariableFanSlot) (current next parent : Nat) :
    groupedVariableIncidenceExpectedCycleElementCodeBlock
        pair current next parent =
      [variableIncidenceCycleElementCode current,
        variableIncidenceCycleElementCode
          (groupedVariableIncidenceCycleSecondKey pair current next)] := by
  by_cases one : pair.1.countPred = 0
  · simp [groupedVariableIncidenceExpectedCycleElementCodeBlock,
      VariableIncidenceLocalControl.expectedCycleSelectors,
      VariableIncidenceLocalControl.ofPair,
      VariableIncidenceLocalControl.current,
      groupedVariableIncidenceCycleSecondKey,
      variableIncidenceCycleElementCode, one]
  · simp [groupedVariableIncidenceExpectedCycleElementCodeBlock,
      VariableIncidenceLocalControl.expectedCycleSelectors,
      VariableIncidenceLocalControl.ofPair,
      VariableIncidenceLocalControl.current,
      VariableIncidenceLocalControl.next,
      groupedVariableIncidenceCycleSecondKey,
      variableIncidenceCycleElementCode, one]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalExpectedCycleIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith4
    groupedVariableIncidenceExpectedCycleElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)).flatten

/-- Globally, the audited current/successor cycle references contain two
copies of every canonical current red cycle element. -/
theorem directSourceFinalExpectedCycleIncidenceElementCodes_perm
    (symbols : List encoding.Γ) :
    (directSourceFinalExpectedCycleIncidenceElementCodes
        decider symbols).Perm
      ((directSourceFinalUniqueFanQueryKeys decider symbols).map
          variableIncidenceCycleElementCode ++
        (directSourceFinalUniqueFanQueryKeys decider symbols).map
          variableIncidenceCycleElementCode) := by
  let pairs := directSourceFinalGroupedVariableFanSlots decider symbols
  let current := directSourceFinalUniqueFanQueryKeys decider symbols
  let next := directSourceFinalGroupedNextOccurrenceKeys decider symbols
  let parents := directSourceFinalGroupedParentIndices decider symbols
  have pairsCurrent : pairs.length = current.length :=
    directSourceFinalGroupedVariableFanSlots_length decider symbols
  have pairsNext : pairs.length = next.length := by
    rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedNextOccurrenceKeys_length]
  have pairsParents : pairs.length = parents.length := by
    rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedParentIndices_length]
  have blockEq :
      groupedVariableIncidenceExpectedCycleElementCodeBlock =
        fun pair current next _ =>
          [variableIncidenceCycleElementCode current] ++
            [variableIncidenceCycleElementCode
              (groupedVariableIncidenceCycleSecondKey
                pair current next)] := by
    funext pair currentKey nextKey parent
    rw [groupedVariableIncidenceExpectedCycleElementCodeBlock_eq]
    rfl
  unfold directSourceFinalExpectedCycleIncidenceElementCodes
  change (List.zipWith4
    groupedVariableIncidenceExpectedCycleElementCodeBlock
    pairs current next parents).flatten.Perm _
  rw [blockEq]
  apply (List.zipWith4_flatten_append_perm
    (fun _ current _ _ => [variableIncidenceCycleElementCode current])
    (fun pair current next _ =>
      [variableIncidenceCycleElementCode
        (groupedVariableIncidenceCycleSecondKey pair current next)])
    pairs current next parents).trans
  have firstEq :
      (List.zipWith4
        (fun _ current _ _ => [variableIncidenceCycleElementCode current])
        pairs current next parents).flatten =
      current.map variableIncidenceCycleElementCode := by
    rw [List.zipWith4_flatten_singleton]
    exact List.zipWith4_project_second_of_lengths
      variableIncidenceCycleElementCode pairs current next parents
      pairsCurrent pairsNext pairsParents
  have secondEq :
      (List.zipWith4
        (fun pair current next _ =>
          [variableIncidenceCycleElementCode
            (groupedVariableIncidenceCycleSecondKey pair current next)])
        pairs current next parents).flatten =
      next.map variableIncidenceCycleElementCode := by
    rw [List.zipWith4_flatten_singleton,
      List.zipWith4_ignore_fourth_of_length_eq
        (fun pair current next =>
          variableIncidenceCycleElementCode
            (groupedVariableIncidenceCycleSecondKey pair current next))
        pairs current next parents pairsParents,
      ← List.map_zipWith3 variableIncidenceCycleElementCode
        groupedVariableIncidenceCycleSecondKey]
    exact congrArg (List.map variableIncidenceCycleElementCode)
      (directSourceFinalGroupedCycleSecondKeys_eq_nextKeys
        decider symbols)
  rw [firstEq, secondEq]
  exact List.Perm.append_left _
    ((directSourceFinalGroupedNextOccurrenceKeys_perm_currentKeys
      decider symbols).map variableIncidenceCycleElementCode)

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFlattenAppendPerm
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceCycleElementSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidencePrivateElementSemantics

/-! # Complete variable-local incidence multiplicities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM

/-- Duplicating a list elementwise is a permutation of two complete copies. -/
theorem duplicateElementCodes_perm_append_self (codes : List Nat) :
    (duplicateElementCodes codes).Perm (codes ++ codes) := by
  induction codes with
  | nil => exact List.Perm.nil
  | cons code codes induction =>
      have expanded :
          ([code, code] ++ duplicateElementCodes codes).Perm
            ([code, code] ++ (codes ++ codes)) :=
        List.Perm.append_left _ induction
      have swap :
          ([code, code] ++ (codes ++ codes)).Perm
            ((code :: codes) ++ (code :: codes)) := by
        have middle : ([code] ++ codes).Perm (codes ++ [code]) :=
          List.perm_append_comm
        simpa only [List.cons_append, List.nil_append,
          List.append_assoc] using
          (middle.append_right codes).append_left [code]
      exact (by
        simpa [duplicateElementCodes] using expanded.trans swap)

/-- Canonical variable elements of one occurrence in local RGB order. -/
def groupedVariableCanonicalElementCodeBlock
    (pair : GroupedVariableFanSlot) (current : Nat) : List Nat :=
  directSourceFinalVariableElementCodeBlock .red pair current ++
    directSourceFinalVariableElementCodeBlock .green pair current ++
    directSourceFinalVariableElementCodeBlock .blue pair current

/-- Duplicating the complete local RGB block separates into the red cycle
head and the already-audited private block. -/
theorem duplicate_groupedVariableCanonicalElementCodeBlock_eq
    (pair : GroupedVariableFanSlot) (current : Nat) :
    duplicateElementCodes
        (groupedVariableCanonicalElementCodeBlock pair current) =
      [variableIncidenceCycleElementCode current,
          variableIncidenceCycleElementCode current] ++
        groupedVariableCanonicalPrivateElementCodes pair current := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [groupedVariableCanonicalElementCodeBlock,
      groupedVariableCanonicalPrivateElementCodes,
      duplicateElementCodes,
      variableIncidenceCycleElementCode,
      directSourceFinalVariableElementCodeBlock,
      directSourceFinalVariableElementCodeCandidateBlock,
      directSourceFinalVariableElementColorTagBase,
      kindEq]

/-- Elementwise duplication commutes with flattening a list of blocks. -/
theorem duplicateElementCodes_flatten (blocks : List (List Nat)) :
    duplicateElementCodes blocks.flatten =
      (blocks.map duplicateElementCodes).flatten := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      change duplicateElementCodes (block ++ blocks.flatten) =
        duplicateElementCodes block ++
          (blocks.map duplicateElementCodes).flatten
      rw [show duplicateElementCodes (block ++ blocks.flatten) =
          duplicateElementCodes block ++
            duplicateElementCodes blocks.flatten by
        exact List.flatMap_append]
      rw [induction]

/-- Duplicating a mapped code column is flattening its mapped pair blocks. -/
theorem duplicateElementCodes_map {Source : Type*}
    (encode : Source → Nat) (items : List Source) :
    duplicateElementCodes (items.map encode) =
      (items.map fun item => [encode item, encode item]).flatten := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.map_cons, List.flatten_cons]
      change [encode item, encode item] ++
          duplicateElementCodes (items.map encode) =
        [encode item, encode item] ++
          (items.map fun item => [encode item, encode item]).flatten
      rw [induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalExpectedPrivateIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith4
    groupedVariableIncidenceExpectedPrivateElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)).flatten

/-- The globally audited variable-local blocks separate into their cycle
and private contributions. -/
theorem directSourceFinalExpectedVariableIncidenceElementCodes_perm_parts
    (symbols : List encoding.Γ) :
    (directSourceFinalExpectedVariableIncidenceElementCodes
        decider symbols).Perm
      (directSourceFinalExpectedCycleIncidenceElementCodes
          decider symbols ++
        directSourceFinalExpectedPrivateIncidenceElementCodes
          decider symbols) := by
  have blockEq :
      groupedVariableIncidenceExpectedVariableElementCodeBlock =
        fun pair current next parent =>
          groupedVariableIncidenceExpectedCycleElementCodeBlock
              pair current next parent ++
            groupedVariableIncidenceExpectedPrivateElementCodeBlock
              pair current next parent := by
    rfl
  unfold directSourceFinalExpectedVariableIncidenceElementCodes
    directSourceFinalExpectedCycleIncidenceElementCodes
    directSourceFinalExpectedPrivateIncidenceElementCodes
  rw [blockEq]
  exact List.zipWith4_flatten_append_perm
    groupedVariableIncidenceExpectedCycleElementCodeBlock
    groupedVariableIncidenceExpectedPrivateElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
    (directSourceFinalGroupedParentIndices decider symbols)

/-- The private contribution drops its unused successor and parent columns
and is exactly the canonical per-occurrence private block stream. -/
theorem directSourceFinalExpectedPrivateIncidenceElementCodes_eq
    (symbols : List encoding.Γ) :
    directSourceFinalExpectedPrivateIncidenceElementCodes decider symbols =
      (List.zipWith groupedVariableCanonicalPrivateElementCodes
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols)).flatten := by
  let pairs := directSourceFinalGroupedVariableFanSlots decider symbols
  let current := directSourceFinalUniqueFanQueryKeys decider symbols
  let next := directSourceFinalGroupedNextOccurrenceKeys decider symbols
  let parents := directSourceFinalGroupedParentIndices decider symbols
  have pairsNext : pairs.length = next.length := by
    rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedNextOccurrenceKeys_length]
  have pairsParents : pairs.length = parents.length := by
    rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedParentIndices_length]
  have blockEq :
      groupedVariableIncidenceExpectedPrivateElementCodeBlock =
        fun pair current _ _ =>
          groupedVariableCanonicalPrivateElementCodes pair current := by
    funext pair currentKey nextKey parent
    exact groupedVariableIncidenceExpectedPrivateElementCodeBlock_eq
      pair currentKey nextKey parent
  unfold directSourceFinalExpectedPrivateIncidenceElementCodes
  change (List.zipWith4
      groupedVariableIncidenceExpectedPrivateElementCodeBlock
      pairs current next parents).flatten = _
  rw [blockEq,
    List.zipWith4_ignore_fourth_of_length_eq
      (fun pair current _ =>
        groupedVariableCanonicalPrivateElementCodes pair current)
      pairs current next parents pairsParents,
    List.zipWith3_ignore_third_of_length_eq
      groupedVariableCanonicalPrivateElementCodes
      pairs current next pairsNext]

def directSourceFinalCanonicalVariableElementCodesPairMajor
    (symbols : List encoding.Γ) : List Nat :=
  (List.zipWith groupedVariableCanonicalElementCodeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalUniqueFanQueryKeys decider symbols)).flatten

set_option maxHeartbeats 800000 in
/-- Pair-major local RGB order is a permutation of the compiler's canonical
color-major variable-element order. -/
theorem directSourceFinalCanonicalVariableElementCodesPairMajor_perm
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalVariableElementCodesPairMajor
        decider symbols).Perm
      (directSourceFinalCanonicalVariableElementCodes
          decider .red symbols ++
        directSourceFinalCanonicalVariableElementCodes
          decider .green symbols ++
        directSourceFinalCanonicalVariableElementCodes
          decider .blue symbols) := by
  let pairs := directSourceFinalGroupedVariableFanSlots decider symbols
  let current := directSourceFinalUniqueFanQueryKeys decider symbols
  let red := fun pair current =>
    directSourceFinalVariableElementCodeBlock .red pair current
  let green := fun pair current =>
    directSourceFinalVariableElementCodeBlock .green pair current
  let blue := fun pair current =>
    directSourceFinalVariableElementCodeBlock .blue pair current
  rw [directSourceFinalCanonicalVariableElementCodes_eq_zipWith,
    directSourceFinalCanonicalVariableElementCodes_eq_zipWith,
    directSourceFinalCanonicalVariableElementCodes_eq_zipWith]
  unfold directSourceFinalCanonicalVariableElementCodesPairMajor
  change (List.zipWith
    (fun pair key => red pair key ++ green pair key ++ blue pair key)
    pairs current).flatten.Perm _
  exact List.zipWith_flatten_append3_perm
    red green blue pairs current

/-- The complete variable-local incidence contribution contains exactly two
references to every canonical variable element. -/
theorem directSourceFinalExpectedVariableIncidenceElementCodes_perm_duplicate
    (symbols : List encoding.Γ) :
    (directSourceFinalExpectedVariableIncidenceElementCodes
        decider symbols).Perm
      (duplicateElementCodes
        (directSourceFinalCanonicalVariableElementCodesPairMajor
          decider symbols)) := by
  let pairs := directSourceFinalGroupedVariableFanSlots decider symbols
  let current := directSourceFinalUniqueFanQueryKeys decider symbols
  let heads := current.map variableIncidenceCycleElementCode
  let privateCodes :=
    (List.zipWith groupedVariableCanonicalPrivateElementCodes
      pairs current).flatten
  apply (directSourceFinalExpectedVariableIncidenceElementCodes_perm_parts
    decider symbols).trans
  apply (List.Perm.append
    (directSourceFinalExpectedCycleIncidenceElementCodes_perm
      decider symbols)
    (List.Perm.refl _)).trans
  change ((heads ++ heads) ++
      directSourceFinalExpectedPrivateIncidenceElementCodes
        decider symbols).Perm _
  rw [directSourceFinalExpectedPrivateIncidenceElementCodes_eq]
  change ((heads ++ heads) ++ privateCodes).Perm _
  apply ((duplicateElementCodes_perm_append_self heads).symm
    |>.append_right privateCodes).trans
  have pairsCurrent : pairs.length = current.length :=
    directSourceFinalGroupedVariableFanSlots_length decider symbols
  have headBlocksEq :
      (List.zipWith
        (fun _ key => [variableIncidenceCycleElementCode key,
          variableIncidenceCycleElementCode key])
        pairs current).flatten = duplicateElementCodes heads := by
    rw [List.zipWith_project_right_of_length_eq
      (fun key => [variableIncidenceCycleElementCode key,
        variableIncidenceCycleElementCode key])
      pairs current pairsCurrent]
    exact (duplicateElementCodes_map
      variableIncidenceCycleElementCode current).symm
  rw [← headBlocksEq]
  apply (List.zipWith_flatten_append_perm
    (fun _ key => [variableIncidenceCycleElementCode key,
      variableIncidenceCycleElementCode key])
    groupedVariableCanonicalPrivateElementCodes
    pairs current).symm.trans
  have blockEq :
      (fun pair key =>
        [variableIncidenceCycleElementCode key,
            variableIncidenceCycleElementCode key] ++
          groupedVariableCanonicalPrivateElementCodes pair key) =
        fun pair key => duplicateElementCodes
          (groupedVariableCanonicalElementCodeBlock pair key) := by
    funext pair key
    exact (duplicate_groupedVariableCanonicalElementCodeBlock_eq
      pair key).symm
  rw [blockEq]
  unfold directSourceFinalCanonicalVariableElementCodesPairMajor
  rw [duplicateElementCodes_flatten, List.map_zipWith]

/-- In the compiler's canonical color-major order, the variable-local
incidence contribution still contains exactly two copies of every variable
element code. -/
theorem directSourceFinalExpectedVariableIncidenceElementCodes_perm_canonical
    (symbols : List encoding.Γ) :
    (directSourceFinalExpectedVariableIncidenceElementCodes
        decider symbols).Perm
      (duplicateElementCodes
        (directSourceFinalCanonicalVariableElementCodes
            decider .red symbols ++
          directSourceFinalCanonicalVariableElementCodes
            decider .green symbols ++
          directSourceFinalCanonicalVariableElementCodes
            decider .blue symbols)) := by
  apply (directSourceFinalExpectedVariableIncidenceElementCodes_perm_duplicate
    decider symbols).trans
  unfold duplicateElementCodes
  exact (directSourceFinalCanonicalVariableElementCodesPairMajor_perm
    decider symbols).flatMap fun code _ => List.Perm.refl [code, code]

end LeanTrominoes.PeriodicCNFStripReduction

end

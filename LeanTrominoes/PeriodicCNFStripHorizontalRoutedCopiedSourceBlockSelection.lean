/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Copied source lookups preserve their parent clause blocks -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderCopiedSourcePosition

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeaderPresentationAtomScope

private theorem expectedAux_map_getD_blocks
    (preceding : List Nat) (blocks : List (DirectedClauseProfile × List Nat))
    (lengths : ∀ block ∈ blocks, block.2.length = sourceWordCount block.1) :
    (expectedAux preceding.length (blocks.map (fun block => Token.clause block.1))).map
        (fun position => (preceding ++ blocks.flatMap Prod.snd).getD position 0) =
      blocks.flatMap (fun block => (clauseBlock block.1).map
        (fun control => block.2.getD (scopeOffset control) 0)) := by
  induction blocks generalizing preceding with
  | nil => rfl
  | cons block blocks ih =>
      have headLength := lengths block (List.mem_cons_self ..)
      have tailLengths : ∀ next ∈ blocks, next.2.length = sourceWordCount next.1 :=
        fun next member => lengths next (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, expectedAux, List.map_append, List.map_map, List.flatMap_cons]
      apply congrArg₂ List.append
      · apply List.map_congr_left
        intro control member
        have offsetLt : scopeOffset control < block.2.length := by
          rw [headLength]
          exact scopeOffset_lt block.1 control member
        simp only [Function.comp_def, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getElem?_append_left offsetLt]
      · have shifted := ih (preceding ++ block.2) tailLengths
        simpa only [List.length_append, headLength, List.append_assoc] using shifted

private theorem totalSourceWordCount_clauseBlocks
    (blocks : List (DirectedClauseProfile × List Nat))
    (lengths : ∀ block ∈ blocks, block.2.length = sourceWordCount block.1) :
    (blocks.flatMap Prod.snd).length =
      totalSourceWordCount (blocks.map (fun block => Token.clause block.1)) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, totalSourceWordCount]
      rw [lengths block (List.mem_cons_self ..), ih]
      exact fun next member => lengths next (List.mem_cons_of_mem _ member)

/-- Selecting from a flattened candidate column is exactly selecting within
each parent clause's own row, using the compiled presentation-relative scope.
No query crosses a clause boundary. -/
theorem selectedValues_clauseBlocks
    (blocks : List (DirectedClauseProfile × List Nat))
    (lengths : ∀ block ∈ blocks, block.2.length = sourceWordCount block.1) :
    selectedValues (blocks.map (fun block => Token.clause block.1))
        (blocks.flatMap Prod.snd) =
      blocks.flatMap (fun block => (clauseBlock block.1).map
        (fun control => block.2.getD (scopeOffset control) 0)) := by
  rw [selectedValues_eq_map_getD _ _ (totalSourceWordCount_clauseBlocks blocks lengths),
    positions_eq_expected]
  simpa only [List.length_nil, List.nil_append, expected] using
    expectedAux_map_getD_blocks [] blocks lengths

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderCopiedSourcePosition

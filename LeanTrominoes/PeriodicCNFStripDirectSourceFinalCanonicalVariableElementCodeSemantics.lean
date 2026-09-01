/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalVariableElementCodeCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of direct final canonical variable-element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM
open Gadget

/-- The three unfiltered codes reserved for one active occurrence. -/
def directSourceFinalVariableElementCodeCandidateBlock
    (color : WireColor) (key : Nat) : List Nat :=
  let base := key * directSourceFinalElementCodeStride
  let tag := directSourceFinalVariableElementColorTagBase color
  [base + (0 + tag), base + (1 + tag), base + (2 + tag)]

/-- The structural codes contributed by one active variable occurrence. -/
def directSourceFinalVariableElementCodeBlock
    (color : WireColor) (pair : GroupedVariableFanSlot)
    (key : Nat) : List Nat :=
  match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
  | .fixedRed => directSourceFinalVariableElementCodeCandidateBlock color key
  | .fixedGreen | .fixedBlue =>
      (directSourceFinalVariableElementCodeCandidateBlock color key).take 1

private theorem directSourceFinalVariableElementCodeCandidates_eq
    (color : WireColor) (keys : List Nat) :
    directSourceFinalVariableElementCodeCandidates color keys =
      keys.flatMap
        (directSourceFinalVariableElementCodeCandidateBlock color) := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      unfold directSourceFinalVariableElementCodeCandidates
        AlignedUnaryListClosure.added
        directSourceFinalVariableElementCandidateBases
        directSourceFinalVariableElementCandidateTags
        UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
        UnaryFieldConstantOffsets.values UnaryFieldThreeSlotRanks.values
        directSourceFinalVariableElementCodeCandidateBlock
      simp only [List.map_cons, List.flatMap_cons, List.replicate_succ,
        List.replicate_zero,
        UnaryAlignedAddMachine.sums, List.cons_append]
      change _ :: _ :: _ ::
          directSourceFinalVariableElementCodeCandidates color keys =
        _ :: _ :: _ ::
          keys.flatMap
            (directSourceFinalVariableElementCodeCandidateBlock color)
      rw [induction]

private theorem selected_variableElementBlocks
    (color : WireColor) (pairs : List GroupedVariableFanSlot)
    (keys : List Nat) (lengthEq : pairs.length = keys.length) :
    DelimitedBinaryWordBooleanFilter.selected
        (pairs.flatMap directSourceFinalVariableElementActiveBlock)
        (keys.flatMap
          (directSourceFinalVariableElementCodeCandidateBlock color)) =
      (List.zipWith (directSourceFinalVariableElementCodeBlock color)
        pairs keys).flatten := by
  induction pairs generalizing keys with
  | nil =>
      have keysEq : keys = [] := List.eq_nil_of_length_eq_zero lengthEq.symm
      subst keys
      rfl
  | cons pair pairs induction =>
      cases keys with
      | nil => simp at lengthEq
      | cons key keys =>
          have tailLength : pairs.length = keys.length := by
            simpa using Nat.succ.inj lengthEq
          cases kindEq : pair.1.kind
              (groupedVariableFanSiteSlot pair.2) <;>
            simp [directSourceFinalVariableElementActiveBlock,
              directSourceFinalVariableElementCodeCandidateBlock,
              directSourceFinalVariableElementCodeBlock, kindEq,
              DelimitedBinaryWordBooleanFilter.selected,
              induction keys tailLength]

private theorem variableElementCodeBlocks_length
    (color : WireColor) (pairs : List GroupedVariableFanSlot)
    (keys : List Nat) (lengthEq : pairs.length = keys.length) :
    ((List.zipWith (directSourceFinalVariableElementCodeBlock color)
        pairs keys).flatten).length =
      (pairs.flatMap directSourceFinalVariableElementDegreeBlock).length := by
  induction pairs generalizing keys with
  | nil =>
      have keysEq : keys = [] := List.eq_nil_of_length_eq_zero lengthEq.symm
      subst keys
      rfl
  | cons pair pairs induction =>
      cases keys with
      | nil => simp at lengthEq
      | cons key keys =>
          have tailLength : pairs.length = keys.length := by
            simpa using Nat.succ.inj lengthEq
          cases kindEq : pair.1.kind
              (groupedVariableFanSiteSlot pair.2) <;>
            simp [directSourceFinalVariableElementCodeBlock,
              directSourceFinalVariableElementCodeCandidateBlock,
              directSourceFinalVariableElementDegreeBlock, kindEq,
              induction keys tailLength]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled column is exactly the variable-local structural-code block
for every grouped active occurrence. -/
theorem directSourceFinalCanonicalVariableElementCodes_eq_zipWith
    (color : WireColor) (symbols : List encoding.Γ) :
    directSourceFinalCanonicalVariableElementCodes decider color symbols =
      (List.zipWith (directSourceFinalVariableElementCodeBlock color)
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols)).flatten := by
  unfold directSourceFinalCanonicalVariableElementCodes
  rw [UnaryFieldBooleanFilter.selectedValues_eq,
    directSourceFinalVariableElementCodeCandidates_eq]
  exact selected_variableElementBlocks color _ _
    (directSourceFinalGroupedVariableFanSlots_length decider symbols)

/-- Variable element codes and their already-compiled degree column have
the same canonical order and length. -/
@[simp] theorem directSourceFinalCanonicalVariableElementCodes_length
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalVariableElementCodes
        decider color symbols).length =
      (directSourceFinalVariableElementDegrees decider symbols).length := by
  rw [directSourceFinalCanonicalVariableElementCodes_eq_zipWith]
  unfold directSourceFinalVariableElementDegrees
    FiniteUnaryFieldBlockMap.values
  exact variableElementCodeBlocks_length color _ _
    (directSourceFinalGroupedVariableFanSlots_length decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end

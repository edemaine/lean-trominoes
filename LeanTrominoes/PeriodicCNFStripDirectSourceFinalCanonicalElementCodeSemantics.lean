/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalVariableElementCodeSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of complete direct final canonical element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget
open PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- The four color-specific structural codes of one final clause. -/
def directSourceFinalClauseElementCodeBlock
    (color : WireColor) (index : Nat) : List Nat :=
  let base := index * directSourceFinalElementCodeStride
  let tag := directSourceFinalClauseElementColorTagBase color
  [base + (0 + tag), base + (1 + tag),
    base + (2 + tag), base + (3 + tag)]

/-- The unary arithmetic pipeline emits exactly four consecutive
color-specific clause-element tags under every clause index. -/
theorem directSourceFinalClauseElementCodesFromIndices_eq_flatMap
    (color : WireColor) (indices : List Nat) :
    directSourceFinalClauseElementCodesFromIndices color indices =
      indices.flatMap (directSourceFinalClauseElementCodeBlock color) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      unfold directSourceFinalClauseElementCodesFromIndices
        AlignedUnaryListClosure.added
        directSourceFinalClauseElementCodeBases
        directSourceFinalClauseElementCodeTags
        UnaryFieldFixedCopies.values UnaryFieldConstantScale.values
        UnaryFieldConstantOffsets.values UnaryFieldFourSlotRanks.values
        directSourceFinalClauseElementCodeBlock
      simp only [List.map_cons, List.flatMap_cons, List.replicate_succ,
        List.replicate_zero, UnaryAlignedAddMachine.sums,
        List.cons_append]
      change _ :: _ :: _ :: _ ::
          directSourceFinalClauseElementCodesFromIndices color indices =
        _ :: _ :: _ :: _ ::
          indices.flatMap (directSourceFinalClauseElementCodeBlock color)
      rw [induction]

@[simp] theorem directSourceFinalClauseElementCodesFromIndices_length
    (color : WireColor) (indices : List Nat) :
    (directSourceFinalClauseElementCodesFromIndices color indices).length =
      4 * indices.length := by
  unfold directSourceFinalClauseElementCodesFromIndices
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalClauseElementCodeBases_length,
    directSourceFinalClauseElementCodeTags_length, min_self]

@[simp] theorem directSourceFinalClauseIndices_length
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIndices decider symbols).length =
      (directSourceFinalClauseIndexPlaceholders decider symbols).length := by
  simp [directSourceFinalClauseIndices, UnaryFieldRange.values]

private theorem four_clausePlaceholders_length_eq_degrees
    (fans : List ClauseRibbonFanData) :
    4 * (FiniteUnaryFieldBlockMap.values
        directSourceFinalClauseIndexPlaceholderBlock fans).length =
      (FiniteUnaryFieldBlockMap.values
        directSourceFinalClauseElementDegreeBlock fans).length := by
  induction fans with
  | nil => rfl
  | cons fan fans induction =>
      rw [show FiniteUnaryFieldBlockMap.values
            directSourceFinalClauseIndexPlaceholderBlock
            (fan :: fans) =
          directSourceFinalClauseIndexPlaceholderBlock fan ++
            FiniteUnaryFieldBlockMap.values
              directSourceFinalClauseIndexPlaceholderBlock fans by rfl]
      rw [show FiniteUnaryFieldBlockMap.values
            directSourceFinalClauseElementDegreeBlock
            (fan :: fans) =
          directSourceFinalClauseElementDegreeBlock fan ++
            FiniteUnaryFieldBlockMap.values
              directSourceFinalClauseElementDegreeBlock fans by rfl]
      rw [List.length_append, List.length_append]
      rw [show (directSourceFinalClauseIndexPlaceholderBlock fan).length = 1
          by rfl,
        directSourceFinalClauseElementDegreeBlock_length]
      omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled clause suffix is four explicit color-specific code fields
per actual final clause, using its zero-based clause index. -/
theorem directSourceFinalClauseElementCodes_eq_flatMap
    (color : WireColor) (symbols : List encoding.Γ) :
    directSourceFinalClauseElementCodes decider color symbols =
      (List.range
        (directSourceFinalClauseIndexPlaceholders
          decider symbols).length).flatMap
        (directSourceFinalClauseElementCodeBlock color) := by
  unfold directSourceFinalClauseElementCodes
    directSourceFinalClauseIndices UnaryFieldRange.values
  exact directSourceFinalClauseElementCodesFromIndices_eq_flatMap color _

/-- Clause structural codes and the clause-degree suffix have identical
canonical internal/top/left/right order and length. -/
@[simp] theorem directSourceFinalClauseElementCodes_length
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalClauseElementCodes
        decider color symbols).length =
      (directSourceFinalClauseElementDegrees decider symbols).length := by
  unfold directSourceFinalClauseElementCodes
    directSourceFinalClauseElementDegrees
  rw [directSourceFinalClauseElementCodesFromIndices_length,
    directSourceFinalClauseIndices_length]
  unfold directSourceFinalClauseIndexPlaceholders
  exact four_clausePlaceholders_length_eq_degrees _

@[simp] theorem directSourceFinalOneColorElementCodes_length
    (color : WireColor) (symbols : List encoding.Γ) :
    (directSourceFinalOneColorElementCodes
        decider color symbols).length =
      (directSourceFinalOneColorElementDegrees decider symbols).length := by
  simp [directSourceFinalOneColorElementCodes,
    directSourceFinalOneColorElementDegrees]

/-- The complete RGB code and degree columns are pointwise aligned. -/
@[simp] theorem directSourceFinalCanonicalElementCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalElementCodes decider symbols).length =
      (directSourceFinalCanonicalElementDegrees decider symbols).length := by
  simp [directSourceFinalCanonicalElementCodes,
    directSourceFinalGreenBlueElementCodes,
    directSourceFinalCanonicalElementDegrees,
    directSourceFinalGreenBlueElementDegrees]

end LeanTrominoes.PeriodicCNFStripReduction

end

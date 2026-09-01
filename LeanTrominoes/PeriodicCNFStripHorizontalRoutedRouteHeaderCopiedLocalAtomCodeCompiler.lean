/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedParentIndexCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderParentLocalAtomCode
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Parent-indexed local atom codes for copied clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderCopiedLocalAtomCode

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader

noncomputable def codeBound : Nat :=
  Fintype.card ParentLocalAtomCode

theorem codeBound_pos : 0 < codeBound := by
  exact Fintype.card_pos

theorem parentLocalAtomCodeIndex_lt (code : ParentLocalAtomCode) :
    parentLocalAtomCodeIndex code < codeBound := by
  exact (Fintype.equivFin ParentLocalAtomCode code).isLt

/-- A base-`codeBound` code for one local atom and its copied parent. -/
noncomputable def localIdentityCode (parent : Nat)
    (control : AtomControl) : Nat :=
  parent * codeBound +
    parentLocalAtomCodeIndex (parentLocalAtomCode control)

/-- Local identity codes are exact: equality means the same parent and the
same represented parent-relative atom. -/
theorem localIdentityCode_eq_iff (firstParent secondParent : Nat)
    (first second : AtomControl) :
    localIdentityCode firstParent first =
        localIdentityCode secondParent second ↔
      firstParent = secondParent ∧
        first.representedAtom = second.representedAtom := by
  let firstIndex :=
    parentLocalAtomCodeIndex (parentLocalAtomCode first)
  let secondIndex :=
    parentLocalAtomCodeIndex (parentLocalAtomCode second)
  have firstLt : firstIndex < codeBound :=
    parentLocalAtomCodeIndex_lt _
  have secondLt : secondIndex < codeBound :=
    parentLocalAtomCodeIndex_lt _
  constructor
  · intro equality
    have indexEquality := congrArg (fun value => value % codeBound) equality
    have indexEq : firstIndex = secondIndex := by
      simpa [localIdentityCode, firstIndex, secondIndex,
        Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt firstLt,
        Nat.mod_eq_of_lt secondLt] using indexEquality
    have parentProducts :
        firstParent * codeBound = secondParent * codeBound := by
      have equality' :
          firstParent * codeBound + firstIndex =
            secondParent * codeBound + secondIndex := by
        simpa [localIdentityCode, firstIndex, secondIndex] using equality
      rw [indexEq] at equality'
      exact Nat.add_right_cancel equality'
    have parentEq : firstParent = secondParent := by
      apply Nat.mul_left_cancel codeBound_pos
      simpa [Nat.mul_comm] using parentProducts
    have codeEq :
        parentLocalAtomCode first = parentLocalAtomCode second :=
      parentLocalAtomCodeIndex_injective indexEq
    exact ⟨parentEq,
      (parentLocalAtomCode_eq_iff first second).mp codeEq⟩
  · rintro ⟨parentEq, representedEq⟩
    subst secondParent
    have codeEq :
        parentLocalAtomCode first = parentLocalAtomCode second :=
      (parentLocalAtomCode_eq_iff first second).mpr representedEq
    simp [localIdentityCode, codeEq]

noncomputable def offset : AtomScopeControl → Nat
  | .inherited _ => 0
  | .parentLocal control =>
      parentLocalAtomCodeIndex (parentLocalAtomCode control)

def offsets (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values offset
    (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)

def scaledParents (source : List Token) : List Nat :=
  UnaryFieldConstantScale.values codeBound
    (HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices source)

/-- The numeric local identity column.  Values at inherited positions are
irrelevant; local positions equal `localIdentityCode`. -/
def codes (source : List Token) : List Nat :=
  AlignedUnaryListClosure.added
    (scaledParents source) (offsets source)

theorem offsets_length (source : List Token) :
    (offsets source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold offsets FiniteUnaryFieldMap.values
  rw [List.length_map,
    HorizontalRoutedRouteHeaderPresentationAtomScope.output_length]

theorem scaledParents_length (source : List Token) :
    (scaledParents source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold scaledParents UnaryFieldConstantScale.values
  rw [List.length_map,
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_length]

theorem codes_length (source : List Token) :
    (codes source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  rw [codes, AlignedUnaryListClosure.added_length,
    scaledParents_length, offsets_length, min_self]

noncomputable def offsetsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields offsets := by
  unfold offsets
  exact TM2CompositionMachine.computableInPolyTime
    HorizontalRoutedRouteHeaderPresentationAtomScope.computableInPolyTime
    (FiniteUnaryFieldMap.computableInPolyTime offset)

noncomputable def scaledParentsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      scaledParents := by
  unfold scaledParents
  exact TM2CompositionMachine.computableInPolyTime
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndicesComputableInPolyTime
    (UnaryFieldConstantScale.computableInPolyTime codeBound)

/-- The complete parent-indexed local-code column is polynomial-time
computable as unary fields. -/
noncomputable def codesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields codes := by
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    id scaledParents offsets
    (fun source => (scaledParents_length source).trans
      (offsets_length source).symm)
    scaledParentsComputableInPolyTime offsetsComputableInPolyTime

end HorizontalRoutedRouteHeaderCopiedLocalAtomCode
end PeriodicCNFStripReduction
end LeanTrominoes

end

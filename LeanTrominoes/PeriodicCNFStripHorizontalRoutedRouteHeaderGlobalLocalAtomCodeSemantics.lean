/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderGlobalLocalOccurrenceBound

/-! # Semantics of globally parent-indexed local atom codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderGlobalLocalAtomCode

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderCopiedLocalAtomCode
open HorizontalRoutedRouteHeaderCopiedParentIndex
open HorizontalRoutedRouteHeaderPresentationAtomScope
open HorizontalRoutedRouteHeaderGlobalLocalAtoms

/-- Keep exactly the values aligned with parent-local scope controls. -/
def selectedLocalCodes :
    List AtomScopeControl → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | .inherited _ :: scopes, _ :: values =>
      selectedLocalCodes scopes values
  | .parentLocal _ :: scopes, value :: values =>
      value :: selectedLocalCodes scopes values

def scopeCode (parent : Nat) : AtomScopeControl → Nat
  | .inherited _ => parent * codeBound
  | .parentLocal control =>
      parent * codeBound +
        parentLocalAtomCodeIndex (parentLocalAtomCode control)

/-- Full aligned numeric column, including harmless values at inherited
positions, in direct blockwise parent order. -/
def codeBlocksAux : Nat → List Token → List Nat
  | _, [] => []
  | parent, .variable :: source => codeBlocksAux parent source
  | parent, .clause profile :: source =>
      (clauseBlock profile).map (scopeCode parent) ++
        codeBlocksAux (parent + 1) source

private theorem sums_scaled_offsets_eq_zipWith
    (parents : List Nat) (scopes : List AtomScopeControl) :
    UnaryAlignedAddMachine.sums
        (parents.map fun parent => parent * codeBound)
        (scopes.map offset) =
      List.zipWith
        (fun parent scope => parent * codeBound + offset scope)
        parents scopes := by
  induction parents generalizing scopes with
  | nil => rfl
  | cons parent parents induction =>
      cases scopes with
      | nil => rfl
      | cons scope scopes =>
          simp only [List.map_cons, UnaryAlignedAddMachine.sums,
            List.zipWith_cons_cons]
          congr 1
          exact induction scopes

/-- The arithmetic compiler is pointwise parent scaling plus the finite local
quotient-code offset. -/
theorem codes_eq_zipWith (source : List Token) :
    codes source =
      List.zipWith
        (fun parent scope => parent * codeBound + offset scope)
        (parentIndices source)
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source) := by
  unfold codes scaledParents offsets AlignedUnaryListClosure.added
    UnaryFieldConstantScale.values FiniteUnaryFieldMap.values
  exact sums_scaled_offsets_eq_zipWith _ _

private theorem zipWith_replicate_append
    (parent : Nat) (scopes : List AtomScopeControl)
    (parents : List Nat) (remaining : List AtomScopeControl) :
    List.zipWith
        (fun current scope => current * codeBound + offset scope)
        (List.replicate scopes.length parent ++ parents)
        (scopes ++ remaining) =
      scopes.map (scopeCode parent) ++
        List.zipWith
          (fun current scope => current * codeBound + offset scope)
          parents remaining := by
  induction scopes with
  | nil => rfl
  | cons scope scopes induction =>
      change
        (parent * codeBound + offset scope) ::
            List.zipWith
              (fun current scope => current * codeBound + offset scope)
              (List.replicate scopes.length parent ++ parents)
              (scopes ++ remaining) =
          scopeCode parent scope ::
            (scopes.map (scopeCode parent) ++
              List.zipWith
                (fun current scope => current * codeBound + offset scope)
                parents remaining)
      congr 1
      cases scope <;> simp [scopeCode, offset]

private theorem zipWith_expected_output_eq_codeBlocksAux
    (parent : Nat) (source : List Token) :
    List.zipWith
        (fun current scope => current * codeBound + offset scope)
        (expectedAux parent source)
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source) =
      codeBlocksAux parent source := by
  induction source generalizing parent with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [expectedAux,
            HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            codeBlocksAux] using induction parent
      | clause profile =>
          let scopes := clauseBlock profile
          let count :=
            (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
              (.clause profile)).length
          have countEq : count = scopes.length := by
            simp [count, scopes]
          have countPos : 0 < count := by
            rw [countEq]
            exact clauseBlock_length_pos profile
          have nextEq : nextParent parent count = parent + 1 := by
            simp [nextParent, Nat.ne_of_gt countPos]
          have nextScopesEq : nextParent parent scopes.length = parent + 1 := by
            rw [← countEq]
            exact nextEq
          simp only [expectedAux,
            HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            List.flatMap_cons, codeBlocksAux]
          change
            List.zipWith
                (fun current scope => current * codeBound + offset scope)
                (List.replicate count parent ++
                  expectedAux (nextParent parent count) source)
                (scopes ++
                  HorizontalRoutedRouteHeaderPresentationAtomScope.output
                    source) = _
          rw [countEq, nextScopesEq, zipWith_replicate_append,
            induction (parent + 1)]

/-- The implemented prefix sums and aligned addition equal the explicit
parent-by-parent code blocks. -/
theorem codes_eq_codeBlocksAux (source : List Token) :
    codes source = codeBlocksAux 0 source := by
  rw [codes_eq_zipWith, parentIndices_eq_expected]
  exact zipWith_expected_output_eq_codeBlocksAux 0 source

private theorem selectedLocalCodes_append
    (firstScopes secondScopes : List AtomScopeControl)
    (firstValues secondValues : List Nat)
    (lengthEq : firstScopes.length = firstValues.length) :
    selectedLocalCodes (firstScopes ++ secondScopes)
        (firstValues ++ secondValues) =
      selectedLocalCodes firstScopes firstValues ++
        selectedLocalCodes secondScopes secondValues := by
  induction firstScopes generalizing firstValues with
  | nil =>
      cases firstValues with
      | nil => rfl
      | cons value values => simp at lengthEq
  | cons scope scopes induction =>
      cases firstValues with
      | nil => simp at lengthEq
      | cons value values =>
          have tailLength : scopes.length = values.length := by
            simpa using Nat.succ.inj lengthEq
          cases scope <;>
            simp [selectedLocalCodes,
              induction values tailLength]

private theorem selectedLocalCodes_map_scopeCode
    (parent : Nat) (scopes : List AtomScopeControl) :
    selectedLocalCodes scopes (scopes.map (scopeCode parent)) =
      ((scopes.filterMap fun scope =>
          match scope with
          | .inherited _ => none
          | .parentLocal control =>
              some (parentLocalAtomCode control)).map fun code =>
        numericCode (parent, code)) := by
  induction scopes with
  | nil => rfl
  | cons scope scopes induction =>
      cases scope <;>
        simp [selectedLocalCodes, scopeCode, numericCode, induction]

private theorem selectedLocalCodes_codeBlocksAux
    (parent : Nat) (source : List Token) :
    selectedLocalCodes
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
        (codeBlocksAux parent source) =
      (atomsAux parent source).map numericCode := by
  induction source generalizing parent with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            codeBlocksAux, atomsAux] using induction parent
      | clause profile =>
          let scopes := clauseBlock profile
          have blockLength :
              scopes.length =
                (scopes.map (scopeCode parent)).length := by simp
          simp only [HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
            List.flatMap_cons, codeBlocksAux, atomsAux, List.map_append]
          rw [selectedLocalCodes_append _ _ _ _ blockLength,
            selectedLocalCodes_map_scopeCode]
          dsimp [scopes]
          have blockEq :
              ((clauseBlock profile).filterMap fun scope =>
                  match scope with
                  | .inherited _ => none
                  | .parentLocal control =>
                      some (parentLocalAtomCode control)).map
                    (fun code => numericCode (parent, code)) =
                (HorizontalRoutedRouteHeaderGlobalLocalAtoms.block
                  parent profile).map numericCode := by
            unfold HorizontalRoutedRouteHeaderGlobalLocalAtoms.block
              parentLocalCodes
            rw [List.map_map]
            apply List.map_congr_left
            intro code codeMember
            rfl
          rw [blockEq]
          congr 1
          exact induction (parent + 1)

/-- Selecting the compiler's parent-local positions yields exactly the
explicit globally indexed semantic atoms under their injective numeric code. -/
theorem selectedLocalCodes_codes_eq_numericCodes (source : List Token) :
    selectedLocalCodes
        (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
        (codes source) =
      numericCodes source := by
  rw [codes_eq_codeBlocksAux]
  exact selectedLocalCodes_codeBlocksAux 0 source

/-- Therefore the actually implemented local-code column, after discarding
its irrelevant inherited positions, has multiplicity at most three. -/
theorem selectedLocalCodes_codes_count_le_three
    (source : List Token) (target : Nat) :
    (selectedLocalCodes
      (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)
      (codes source)).count target <= 3 := by
  rw [selectedLocalCodes_codes_eq_numericCodes]
  exact numericCodes_count_le_three source target

end HorizontalRoutedRouteHeaderGlobalLocalAtomCode
end PeriodicCNFStripReduction
end LeanTrominoes

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderGlobalLocalAtomCodeSemantics

/-! # Parent-local codes projected from coherent source occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderGlobalLocalAtomCode
open HorizontalRoutedRouteHeaderPresentationAtomScope

/-- The arithmetic local-code field selected by a record's own parent and
header. Inherited records retain the compiler's unused parent-only value. -/
def sourceOccurrenceLocalAtomCode (occurrence : SourceOccurrence) : Nat :=
  scopeCode occurrence.parentClauseIndex (outputAtomScopeControl occurrence.header)

private theorem scopeCode_remap (parent : Nat)
    (profile : DirectedClauseProfile) (scope : AtomScopeControl) :
    scopeCode parent (remapScopeControl profile scope) = scopeCode parent scope := by
  cases scope <;> rfl

/-- The numeric local-code compiler and the coherent occurrence enumeration
use the same parent index at every output position. -/
theorem sourceOccurrencesFrom_map_localAtomCode
    (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection))) :
    (sourceOccurrencesFrom parent start source tails).map sourceOccurrenceLocalAtomCode =
      codeBlocksAux parent source := by
  induction source generalizing parent start tails with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | «variable» => exact ih parent start tails
      | clause profile =>
          simp only [sourceOccurrencesFrom, List.map_append, List.map_map,
            codeBlocksAux, clauseBlock, ih, Function.comp_def,
            sourceOccurrenceLocalAtomCode, scopeCode_remap]

theorem sourceOccurrences_map_localAtomCode
    (source : List Token) (tails : List (List (List AxisDirection))) :
    (sourceOccurrences source tails).map sourceOccurrenceLocalAtomCode =
      HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes source := by
  rw [codes_eq_codeBlocksAux]
  exact sourceOccurrencesFrom_map_localAtomCode 0 0 source tails

private theorem codeBlocksAux_variables (parent count : Nat) :
    codeBlocksAux parent (List.replicate count Token.variable) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [List.replicate_succ, codeBlocksAux] using ih

private theorem codeBlocksAux_append_variables
    (parent : Nat) (source : List Token) (count : Nat) :
    codeBlocksAux parent (source ++ List.replicate count Token.variable) =
      codeBlocksAux parent source := by
  induction source generalizing parent with
  | nil => simpa only [List.nil_append, codeBlocksAux] using codeBlocksAux_variables parent count
  | cons token rest ih =>
      cases token <;> simp [codeBlocksAux, ih]

/-- Trailing variable markers create no clauses and cannot change any local
atom's parent index or code. -/
theorem localAtomCodes_append_variables (source : List Token) (count : Nat) :
    HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes
        (source ++ List.replicate count Token.variable) =
      HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes source := by
  rw [codes_eq_codeBlocksAux, codes_eq_codeBlocksAux]
  exact codeBlocksAux_append_variables 0 source count

end LeanTrominoes.PeriodicCNFStripReduction

end

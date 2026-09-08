/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeySemantics
import LeanTrominoes.StableOccurrenceRanksPartition

/-! # Compiled occurrence counts and ranks agree with horizontal source order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance stableHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance stableHorizontalVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

/-- Coherent records and actual horizontal atoms share the same incidence positions. -/
theorem directSourceFinalOccurrences_length_eq_horizontalAtoms (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).length =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
  have lengths := congrArg List.length (directSourceFinalOccurrences_map_atom_eq_horizontal decider symbols)
  simpa only [List.length_map] using lengths

/-- The numeric identity stream covers exactly the actual horizontal atom stream. -/
theorem directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms (symbols : List encoding.Γ) :
    (directSourceFinalAtomIdentityCodes decider symbols).length =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
  rw [directSourceFinalAtomIdentityCodes_length, ← directSourceFinalOccurrences_length_eq_compiled,
    directSourceFinalOccurrences_length_eq_horizontalAtoms]

/-- Equality of numeric identities at any two genuine positions is exactly
horizontal atom equality at those positions. -/
theorem directSourceFinalAtomIdentityCodes_partition_horizontal
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalAtomIdentityCodes decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalAtomIdentityCodes decider symbols).length) :
    (directSourceFinalAtomIdentityCodes decider symbols)[firstIndex] =
        (directSourceFinalAtomIdentityCodes decider symbols)[secondIndex] ↔
      ((horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]'(by
          rw [← directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms]; exact firstLt)) =
      ((horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]'(by
          rw [← directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms]; exact secondLt)) := by
  have firstOccurrenceLt : firstIndex < (directSourceFinalOccurrences decider symbols).length := by
    rwa [directSourceFinalAtomIdentityCodes_length, ← directSourceFinalOccurrences_length_eq_compiled] at firstLt
  have secondOccurrenceLt : secondIndex < (directSourceFinalOccurrences decider symbols).length := by
    rwa [directSourceFinalAtomIdentityCodes_length, ← directSourceFinalOccurrences_length_eq_compiled] at secondLt
  have firstHorizontalLt : firstIndex < (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
    rwa [← directSourceFinalOccurrences_length_eq_horizontalAtoms]
  have secondHorizontalLt : secondIndex < (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
    rwa [← directSourceFinalOccurrences_length_eq_horizontalAtoms]
  have comparison := directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms
    decider symbols firstIndex secondIndex firstOccurrenceLt secondOccurrenceLt _ _
    (List.getElem?_eq_getElem firstHorizontalLt) (List.getElem?_eq_getElem secondHorizontalLt)
  simpa only [List.getD_eq_getElem _ _ firstLt, List.getD_eq_getElem _ _ secondLt] using comparison

/-- The compiled stable rank is the number of earlier incidences of the same
actual horizontal variable, in the actual clause/literal presentation order. -/
theorem directSourceFinalOccurrenceStableRanks_eq_horizontalAtoms (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceStableRanks decider symbols =
      StableOccurrenceRanks.ranks (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences := by
  rw [directSourceFinalOccurrenceStableRanks_eq_identityCodes]
  exact StableOccurrenceRanks.ranks_eq_of_partition _ _
    (directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols)
    (directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols)

/-- Every compiled group size is the total multiplicity of that incidence's
actual horizontal atom. -/
theorem directSourceFinalOccurrenceGroupSizes_eq_horizontalAtoms (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceGroupSizes decider symbols =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
        (fun atom => (horizontalRoutedFormulaComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom) := by
  have identified := StableOccurrenceRanks.multiplicities_eq_of_partition
    (directSourceFinalAtomIdentityCodes decider symbols)
    (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences
    (directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols)
    (directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols)
  rw [directSourceFinalOccurrenceGroupSizes_eq_identityCodes]
  -- The structural BEq and the DecidableEq-derived BEq have the same predicate.
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using identified

end LeanTrominoes.PeriodicCNFStripReduction

end

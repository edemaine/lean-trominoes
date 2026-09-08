/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceStableRankHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityOccurrenceBound
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedAtomOccurrences
import LeanTrominoes.StableOccurrenceRanksPartitionLookup

/-! # Direct fan rank queries recover actual normalized occurrence indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance fanRankLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- A genuine fan rank query selects the exact global occurrence index used
by the actual padded, normalized source's variable occurrence list. -/
theorem directSourceFinalOccurrenceCandidateKeys_idxOf_rank_normalized
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom)
    (rank : Nat)
    (rankLt : rank < (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom) :
    (directSourceFinalOccurrenceCandidateKeys decider symbols).idxOf
        ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + rank) =
      (((horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.idxsOf atom).getD rank 0) := by
  rw [horizontalSemanticNormalizedRibbonSource_variableOccurrences] at atomLookup rankLt ⊢
  obtain ⟨atomLt, atomEq⟩ := List.getElem?_eq_some_iff.mp atomLookup
  have codeLt : index < (directSourceFinalAtomIdentityCodes decider symbols).length := by
    rw [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms]
    exact atomLt
  have identified := StableOccurrenceRanks.candidateKeys_idxOf_rank_of_partition
    (directSourceFinalAtomIdentityCodes decider symbols)
    (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences
    (directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols)
    (directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols)
    (fun value _member => directSourceFinalAtomIdentityCodes_count_le_three decider symbols value)
    index codeLt rank (by
      simpa only [atomEq, List.count_eq_countP, Bool.beq_eq_decide_eq] using rankLt)
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  simpa only [List.getD_eq_getElem _ _ codeLt, atomEq, List.idxsOf, Bool.beq_eq_decide_eq] using identified

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanQueryRankKeyPermutation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityOccurrenceBound
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Exact grouped occurrence-key coverage -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The stable variable-major fan keys are a permutation of the complete
clause-major occurrence-key column.  Thus regrouping neither loses nor
duplicates any genuine final occurrence. -/
theorem directSourceFinalUniqueFanQueryKeys_perm_candidateKeys
    (symbols : List encoding.Γ) :
    (directSourceFinalUniqueFanQueryKeys decider symbols).Perm
      (directSourceFinalOccurrenceCandidateKeys decider symbols) := by
  rw [directSourceFinalUniqueFanQueryKeys_eq,
    directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  apply FinalFanQueryRanks.dedup_keyedBlocks_perm_candidateKeys
  intro value _valueMember
  exact directSourceFinalAtomIdentityCodes_count_le_three
    decider symbols value

end LeanTrominoes.PeriodicCNFStripReduction

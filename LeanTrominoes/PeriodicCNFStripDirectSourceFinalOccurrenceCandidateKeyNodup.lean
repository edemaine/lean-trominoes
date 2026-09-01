/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityOccurrenceBound
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeySemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Uniqueness of direct final occurrence candidate keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete direct final base-three occurrence-key column is
duplicate-free. -/
theorem directSourceFinalOccurrenceCandidateKeys_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceCandidateKeys decider symbols).Nodup := by
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  apply StableOccurrenceRanks.candidateKeys_nodup_of_count_le_three
  intro value valueMember
  exact directSourceFinalAtomIdentityCodes_count_le_three
    decider symbols value

end LeanTrominoes.PeriodicCNFStripReduction

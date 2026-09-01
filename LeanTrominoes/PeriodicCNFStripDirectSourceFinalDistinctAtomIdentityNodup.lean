/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDistinctAtomIdentitySemantics

/-! # Duplicate-free direct distinct final-source identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDistinctIdentityNodupVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The canonical numeric identities of the distinct retained source atoms
are themselves duplicate-free. -/
theorem directSourceFinalDistinctAtomIdentityIndices_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalDistinctAtomIdentityIndices
      decider symbols).Nodup := by
  rw [directSourceFinalDistinctAtomIdentityIndices_eq_dedup_map]
  apply (List.nodup_dedup
    (directSourceFinalCompactOccurrenceAtomWords
      decider symbols).words).map_on
  intro first firstMember second secondMember identityEq
  unfold directSourceFinalCompactAtomIdentityDatum at identityEq
  exact (LastTrueUnaryValueLookupMachine.lookup_equalityRow_range_eq_iff
    (directSourceFinalCompactOccurrenceAtomWords decider symbols).words
    first second
    (List.mem_dedup.mp firstMember)
    (List.mem_dedup.mp secondMember)).mp (by
      simpa [LastRepresentativeEqualityRows.equalityRow,
        StableOccurrenceRanks.equalityRow] using identityEq)

end LeanTrominoes.PeriodicCNFStripReduction

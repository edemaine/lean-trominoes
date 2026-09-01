/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLastIndexIdentitySemantics
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDistinctAtomIdentityCompiler

/-! # Semantics of direct distinct final-source identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Canonical last-index identity attached to one compact source word. -/
noncomputable def directSourceFinalCompactAtomIdentityDatum
    (symbols : List encoding.Γ) (word : List Bool) : Nat :=
  LastTrueUnaryValueLookupMachine.lookup
    (LastRepresentativeEqualityRows.equalityRow
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words
      word)
    (List.range
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words.length)

/-- Representative lookup emits exactly one canonical identity per distinct
compact source word. -/
theorem directSourceFinalDistinctAtomIdentityIndices_eq_dedup_map
    (symbols : List encoding.Γ) :
    directSourceFinalDistinctAtomIdentityIndices decider symbols =
      (directSourceFinalCompactOccurrenceAtomWords
        decider symbols).words.dedup.map
          (directSourceFinalCompactAtomIdentityDatum decider symbols) := by
  unfold directSourceFinalDistinctAtomIdentityIndices
    directSourceFinalCompactOccurrenceAtomIdentityIndices
  rw [DelimitedBinaryWordLastIndexIdentity.identityIndices_eq_map]
  exact
    DelimitedBinaryWordRepresentativeValueLookup.selectedValues_map_eq_dedup_map
      _ _

@[simp] theorem directSourceFinalDistinctAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalDistinctAtomIdentityIndices decider symbols).length =
      (directSourceFinalCompactOccurrenceAtomWords
        decider symbols).words.dedup.length := by
  rw [directSourceFinalDistinctAtomIdentityIndices_eq_dedup_map]
  simp

end LeanTrominoes.PeriodicCNFStripReduction

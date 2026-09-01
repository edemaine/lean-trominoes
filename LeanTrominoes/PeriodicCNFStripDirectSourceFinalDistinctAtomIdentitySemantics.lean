/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLastIndexIdentitySemantics
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDistinctAtomIdentityCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalDistinctAtomWordSemantics

/-! # Semantics of direct distinct final-source identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDistinctAtomIdentitySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

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

/-- The distinct compact-atom identities and the Figure 9 variable markers
have the same stable retained-variable order and, in particular, the same
length. -/
theorem directSourceFinalDistinctAtomIdentityIndices_length_eq_markers
    (symbols : List encoding.Γ) :
    (directSourceFinalDistinctAtomIdentityIndices decider symbols).length =
      (directRetainedFigureNineFiniteSourceVariableMarkers
        decider symbols).length := by
  rw [directSourceFinalDistinctAtomIdentityIndices_length]
  unfold directSourceFinalCompactOccurrenceAtomWords
  rw [PeriodicEightOccurrenceSplit.retainedOccurrenceGlobalAtomWords_dedup_eq]
  · simp only [List.length_map]
    unfold directRetainedFigureNineFiniteSourceVariableMarkers
    simp only [List.length_replicate]
    rw [PeriodicEightOccurrenceSplit.sourceVariables_eq_variableOccurrences_dedup]
    rfl
  · exact directSourceFinalCompactOccurrenceAtomWords_separate
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

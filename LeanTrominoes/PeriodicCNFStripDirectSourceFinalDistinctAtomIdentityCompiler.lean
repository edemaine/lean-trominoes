/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomIdentityCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct identities of distinct final-source atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDistinctAtomIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One canonical last-index identity per distinct pre-Figure9 source atom,
in stable last-occurrence order. -/
def directSourceFinalDistinctAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordRepresentativeValueLookup.selectedValues
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols)

theorem directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_words
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomIdentityIndices
      decider symbols).length =
      (directSourceFinalCompactOccurrenceAtomWords
        decider symbols).words.length := by
  unfold directSourceFinalCompactOccurrenceAtomIdentityIndices
  exact DelimitedBinaryWordLastIndexIdentity.identityIndices_length _

/-- The stable distinct-atom identity column is polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalDistinctAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalDistinctAtomIdentityIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalDistinctAtomIdentityIndices
    exact
      DelimitedBinaryWordRepresentativeValueLookup.selectedValuesComputableInPolyTime
        id
        (directSourceFinalCompactOccurrenceAtomWords decider)
        (directSourceFinalCompactOccurrenceAtomIdentityIndices decider)
        (directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_words
          decider)
        (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime
          decider)
        (directSourceFinalCompactOccurrenceAtomIdentityIndicesComputableInPolyTime
          decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

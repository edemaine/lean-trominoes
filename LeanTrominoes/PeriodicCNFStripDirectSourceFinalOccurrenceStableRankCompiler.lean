/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentitySemantics
import LeanTrominoes.StableOccurrenceRanks
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Stable within-atom ranks of final routed occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceStableRankStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Length-coded binary words of the globally scoped final atom identities. -/
def directSourceFinalAtomIdentityWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  UnaryFieldBinaryWords.words
    (directSourceFinalAtomIdentityCodes decider symbols)

/-- Recover one equality row per final occurrence. -/
def directSourceFinalAtomIdentityEqualityRows
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWordEqualitySquare.rows
    (directSourceFinalAtomIdentityWords decider symbols)

/-- Number of earlier final occurrences carrying the same global atom
identity, in final clause/literal presentation order. -/
def directSourceFinalOccurrenceStableRanks
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts
    (directSourceFinalAtomIdentityEqualityRows decider symbols)

/-- Square reshaping recovers the ordinary equality row of every identity. -/
theorem directSourceFinalAtomIdentityEqualityRows_words
    (symbols : List encoding.Γ) :
    (directSourceFinalAtomIdentityEqualityRows decider symbols).words =
      (directSourceFinalAtomIdentityWords decider symbols).words.map
        (StableOccurrenceRanks.equalityRow
          (directSourceFinalAtomIdentityWords decider symbols).words) := by
  unfold directSourceFinalAtomIdentityEqualityRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  rfl

/-- The compiled prefix counts are exactly the stable ranks of the injective
length-word representation of each identity. -/
theorem directSourceFinalOccurrenceStableRanks_eq
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceStableRanks decider symbols =
      StableOccurrenceRanks.ranks
        (directSourceFinalAtomIdentityWords decider symbols).words := by
  unfold directSourceFinalOccurrenceStableRanks
    DelimitedBinaryWordPrefixTrueCounts.counts
  rw [directSourceFinalAtomIdentityEqualityRows_words]
  exact StableOccurrenceRanks.trueCountsAux_equalityRows
    (directSourceFinalAtomIdentityWords decider symbols).words
    (directSourceFinalAtomIdentityWords decider symbols).words 0

private theorem stableRanksAux_length
    {Value : Type} [DecidableEq Value]
    (all remaining : List Value) (index : Nat) :
    (StableOccurrenceRanks.ranksAux all index remaining).length =
      remaining.length := by
  induction remaining generalizing index with
  | nil => rfl
  | cons value remaining induction =>
      simp [StableOccurrenceRanks.ranksAux, induction]

@[simp] theorem directSourceFinalOccurrenceStableRanks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceStableRanks decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalOccurrenceStableRanks_eq]
  unfold StableOccurrenceRanks.ranks
  rw [stableRanksAux_length]
  unfold directSourceFinalAtomIdentityWords UnaryFieldBinaryWords.words
  rw [List.length_map]
  exact directSourceFinalAtomIdentityCodes_length decider symbols

/-- Final identity length words are polynomial-time computable. -/
noncomputable def
    directSourceFinalAtomIdentityWordsComputableInPolyTime :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalAtomIdentityWords decider) := by
  unfold directSourceFinalAtomIdentityWords
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalAtomIdentityCodesComputableInPolyTime decider)
    UnaryFieldBinaryWords.wordsComputableInPolyTime

/-- Equality rows of all final atom-identity words are polynomial-time. -/
noncomputable def
    directSourceFinalAtomIdentityEqualityRowsComputableInPolyTime :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalAtomIdentityEqualityRows decider) := by
  unfold directSourceFinalAtomIdentityEqualityRows
  exact DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
    id
    (directSourceFinalAtomIdentityWords decider)
    (directSourceFinalAtomIdentityWordsComputableInPolyTime decider)

/-- Stable within-identity ranks of all final occurrences are polynomial-time
computable as unary fields, including for an empty source alphabet. -/
noncomputable def
    directSourceFinalOccurrenceStableRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceStableRanks decider) := by
  unfold directSourceFinalOccurrenceStableRanks
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalAtomIdentityEqualityRowsComputableInPolyTime decider)
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

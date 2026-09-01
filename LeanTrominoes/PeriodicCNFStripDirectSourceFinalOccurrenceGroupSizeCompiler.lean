/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceStableRankCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Final occurrence-group sizes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceGroupSizeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Total number of final occurrences carrying each occurrence's global atom
identity, repeated in final presentation order. -/
def directSourceFinalOccurrenceGroupSizes
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (directSourceFinalAtomIdentityEqualityRows decider symbols)

private theorem countTrue_equalityRow
    (words : List (List Bool)) (word : List Bool) :
    DelimitedBinaryWordTrueCounts.countTrue
        (StableOccurrenceRanks.equalityRow words word) =
      words.count word := by
  unfold DelimitedBinaryWordTrueCounts.countTrue
    StableOccurrenceRanks.equalityRow
  induction words with
  | nil => rfl
  | cons head words induction =>
      by_cases same : word = head
      · subst head
        simp [induction]
      · have headNe : head ≠ word := Ne.symm same
        simp [same, headNe, induction]

private theorem trueCounts_equalityRows
    (words : List (List Bool)) :
    (words.map (StableOccurrenceRanks.equalityRow words)).map
        DelimitedBinaryWordTrueCounts.countTrue =
      words.map fun word => words.count word := by
  rw [List.map_map]
  apply List.map_congr_left
  intro word _wordMember
  exact countTrue_equalityRow words word

/-- Every emitted size is the ordinary multiplicity of that occurrence's
injective identity word. -/
theorem directSourceFinalOccurrenceGroupSizes_eq
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceGroupSizes decider symbols =
      (directSourceFinalAtomIdentityWords decider symbols).words.map
        fun word =>
          (directSourceFinalAtomIdentityWords decider symbols).words.count
            word := by
  unfold directSourceFinalOccurrenceGroupSizes
    DelimitedBinaryWordTrueCounts.counts
  rw [directSourceFinalAtomIdentityEqualityRows_words]
  exact trueCounts_equalityRows
    (directSourceFinalAtomIdentityWords decider symbols).words

@[simp] theorem directSourceFinalOccurrenceGroupSizes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceGroupSizes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalOccurrenceGroupSizes_eq, List.length_map]
  unfold directSourceFinalAtomIdentityWords UnaryFieldBinaryWords.words
  rw [List.length_map]
  exact directSourceFinalAtomIdentityCodes_length decider symbols

/-- The aligned final occurrence-group sizes are polynomial-time computable
as unary fields. -/
noncomputable def
    directSourceFinalOccurrenceGroupSizesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceGroupSizes decider) := by
  unfold directSourceFinalOccurrenceGroupSizes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalAtomIdentityEqualityRowsComputableInPolyTime decider)
    DelimitedBinaryWordTrueCounts.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

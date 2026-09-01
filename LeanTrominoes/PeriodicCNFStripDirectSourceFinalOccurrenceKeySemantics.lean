/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeyCompiler
import LeanTrominoes.StableOccurrenceRankCandidateKeys

/-! # Numeric semantics of final occurrence keys and counts -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem unaryFieldBinaryWord_injective :
    Function.Injective UnaryFieldBinaryWords.word := by
  intro first second wordEq
  have lengthEq := congrArg List.length wordEq
  simpa [UnaryFieldBinaryWords.word] using lengthEq

/-- The compiled stable ranks can equivalently be read directly on the
numeric identity-code column. -/
theorem directSourceFinalOccurrenceStableRanks_eq_identityCodes
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceStableRanks decider symbols =
      StableOccurrenceRanks.ranks
        (directSourceFinalAtomIdentityCodes decider symbols) := by
  rw [directSourceFinalOccurrenceStableRanks_eq]
  unfold directSourceFinalAtomIdentityWords UnaryFieldBinaryWords.words
  apply StableOccurrenceRanks.ranks_map_injective
  exact unaryFieldBinaryWord_injective

/-- The compiled final candidate-key stream is exactly the generic stable
base-three occurrence-key column. -/
theorem directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceCandidateKeys decider symbols =
      StableOccurrenceRanks.candidateKeys
        (directSourceFinalAtomIdentityCodes decider symbols) := by
  rw [directSourceFinalOccurrenceCandidateKeys_eq_zipWith,
    directSourceFinalOccurrenceStableRanks_eq_identityCodes]
  unfold StableOccurrenceRanks.candidateKeys
  generalize StableOccurrenceRanks.ranks
      (directSourceFinalAtomIdentityCodes decider symbols) = ranks
  generalize directSourceFinalAtomIdentityCodes decider symbols = values
  induction values generalizing ranks with
  | nil => simp
  | cons value values induction =>
      cases ranks with
      | nil => rfl
      | cons rank ranks => simp [induction]

/-- Group sizes are ordinary multiplicities in the numeric identity-code
column, because its length-word representation is injective. -/
theorem directSourceFinalOccurrenceGroupSizes_eq_identityCodes
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceGroupSizes decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).map fun code =>
        (directSourceFinalAtomIdentityCodes decider symbols).count code := by
  rw [directSourceFinalOccurrenceGroupSizes_eq]
  unfold directSourceFinalAtomIdentityWords UnaryFieldBinaryWords.words
  generalize directSourceFinalAtomIdentityCodes decider symbols = codes
  change (codes.map UnaryFieldBinaryWords.word).map
      (fun word => (codes.map UnaryFieldBinaryWords.word).count word) =
    codes.map fun code => codes.count code
  rw [List.map_map]
  apply List.map_congr_left
  intro code _codeMember
  exact List.count_map_of_injective
    codes UnaryFieldBinaryWords.word unaryFieldBinaryWord_injective code

/-- Fan count predecessors are the bounded predecessors of numeric identity
multiplicities. -/
theorem directSourceFinalOccurrenceCountPreds_eq_identityCodes
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceCountPreds decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).map fun code =>
        BoundedPositiveCountPreds.boundedPositiveCountPred
          ((directSourceFinalAtomIdentityCodes decider symbols).count code) := by
  generalize codesEq :
    directSourceFinalAtomIdentityCodes decider symbols = codes
  unfold directSourceFinalOccurrenceCountPreds
    BoundedPositiveCountPreds.countPreds
  rw [directSourceFinalOccurrenceGroupSizes_eq_identityCodes, codesEq,
    List.map_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

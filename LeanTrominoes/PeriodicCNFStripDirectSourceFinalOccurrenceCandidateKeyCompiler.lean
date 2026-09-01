/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceStableRankCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryAlignedAddSemantics
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Unique keyed-lookup candidates for final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceCandidateKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Reserve three consecutive keys for every globally scoped atom identity. -/
def directSourceFinalScaledAtomIdentityCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 3
    (directSourceFinalAtomIdentityCodes decider symbols)

/-- Key of every final occurrence: its global identity block plus its stable
zero-based occurrence rank. -/
def directSourceFinalOccurrenceCandidateKeys
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalScaledAtomIdentityCodes decider symbols)
    (directSourceFinalOccurrenceStableRanks decider symbols)

@[simp] theorem directSourceFinalScaledAtomIdentityCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalScaledAtomIdentityCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalScaledAtomIdentityCodes
    UnaryFieldConstantScale.values
  rw [List.length_map, directSourceFinalAtomIdentityCodes_length]

@[simp] theorem directSourceFinalOccurrenceCandidateKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceCandidateKeys decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceCandidateKeys
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalScaledAtomIdentityCodes_length,
    directSourceFinalOccurrenceStableRanks_length, min_self]

/-- Candidate keys are ordinary pointwise `3 * identity + rank` values. -/
theorem directSourceFinalOccurrenceCandidateKeys_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceCandidateKeys decider symbols =
      List.zipWith (· + ·)
        ((directSourceFinalAtomIdentityCodes decider symbols).map
          fun identity => identity * 3)
        (directSourceFinalOccurrenceStableRanks decider symbols) := by
  unfold directSourceFinalOccurrenceCandidateKeys
    directSourceFinalScaledAtomIdentityCodes
    UnaryFieldConstantScale.values AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [List.length_map, directSourceFinalAtomIdentityCodes_length,
      directSourceFinalOccurrenceStableRanks_length])

/-- Base-three occurrence keys recover both components whenever the rank is
in the semantic range zero through two. -/
theorem occurrenceCandidateKey_eq_iff
    (firstIdentity secondIdentity firstRank secondRank : Nat)
    (firstRankLt : firstRank < 3) (secondRankLt : secondRank < 3) :
    firstIdentity * 3 + firstRank = secondIdentity * 3 + secondRank ↔
      firstIdentity = secondIdentity ∧ firstRank = secondRank := by
  constructor
  · intro equal
    have residues := congrArg (fun value : Nat => value % 3) equal
    simp [Nat.add_mod,
      Nat.mod_eq_of_lt firstRankLt,
      Nat.mod_eq_of_lt secondRankLt] at residues
    constructor
    · omega
    · exact residues
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def
    directSourceFinalScaledAtomIdentityCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalScaledAtomIdentityCodes decider) := by
  unfold directSourceFinalScaledAtomIdentityCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalAtomIdentityCodesComputableInPolyTime decider)
    (UnaryFieldConstantScale.computableInPolyTime 3)

/-- Complete final occurrence candidate keys are polynomial-time computable,
including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalOccurrenceCandidateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceCandidateKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOccurrenceCandidateKeys
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalScaledAtomIdentityCodes decider)
      (directSourceFinalOccurrenceStableRanks decider)
      (fun symbols => by
        rw [directSourceFinalScaledAtomIdentityCodes_length,
          directSourceFinalOccurrenceStableRanks_length])
      (directSourceFinalScaledAtomIdentityCodesComputableInPolyTime decider)
      (directSourceFinalOccurrenceStableRanksComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end

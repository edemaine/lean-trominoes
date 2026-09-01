/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCountPredCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler

/-! # Three keyed-lookup queries for every final variable fan -/

noncomputable section

namespace LeanTrominoes

namespace FinalFanQueryRanks

open Computability Turing

/-- Inactive fan slots reuse the final active occurrence. -/
def selectedRank (countPred slot : Fin 3) : Fin 3 :=
  if slot.val ≤ countPred.val then slot else countPred

/-- Requested ranks for the first, second, and third finite fan slots. -/
def block (countPred : Fin 3) : List (Fin 3) :=
  ([0, 1, 2] : List (Fin 3)).map (selectedRank countPred)

def finiteRanks (countPreds : List (Fin 3)) : List (Fin 3) :=
  countPreds.flatMap block

def ranks (countPreds : List (Fin 3)) : List Nat :=
  (finiteRanks countPreds).map Fin.val

@[simp] theorem block_length (countPred : Fin 3) :
    (block countPred).length = 3 := by
  simp [block]

@[simp] theorem ranks_length (countPreds : List (Fin 3)) :
    (ranks countPreds).length = 3 * countPreds.length := by
  simp [ranks, finiteRanks, Nat.mul_comm]

@[simp] theorem block_zero : block 0 = [0, 0, 0] := by
  rfl

@[simp] theorem block_one : block 1 = [0, 1, 1] := by
  rfl

@[simp] theorem block_two : block 2 = [0, 1, 2] := by
  rfl

/-- Expanding the three finite ranks and encoding their values as unary
fields is polynomial-time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields ranks := by
  let expanded : TM2ComputableInPolyTime id id finiteRanks :=
    FiniteBlockTransducer.computableInPolyTime block
  let encoded := TM2CompositionMachine.computableInPolyTime expanded
    (FiniteUnaryFieldMap.computableInPolyTime Fin.val)
  unfold ranks
  simpa only [FiniteUnaryFieldMap.values] using encoded

end FinalFanQueryRanks

namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFanQueryKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Repeat each scaled identity base once for each finite fan slot. -/
def directSourceFinalFanQueryIdentityBases
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldFixedCopies.values 3
    (directSourceFinalScaledAtomIdentityCodes decider symbols)

/-- Three selected occurrence ranks for every final occurrence's fan view. -/
def directSourceFinalFanQueryRanks
    (symbols : List encoding.Γ) : List Nat :=
  FinalFanQueryRanks.ranks
    (directSourceFinalOccurrenceCountPreds decider symbols)

/-- Three composite atom-identity/rank queries for every final occurrence. -/
def directSourceFinalFanQueryKeys
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalFanQueryIdentityBases decider symbols)
    (directSourceFinalFanQueryRanks decider symbols)

@[simp] theorem directSourceFinalFanQueryIdentityBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanQueryIdentityBases decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanQueryIdentityBases
    UnaryFieldFixedCopies.values
  simp [directSourceFinalScaledAtomIdentityCodes_length, Nat.mul_comm]

@[simp] theorem directSourceFinalFanQueryRanks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanQueryRanks decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanQueryRanks
  rw [FinalFanQueryRanks.ranks_length,
    directSourceFinalOccurrenceCountPreds_length]

@[simp] theorem directSourceFinalFanQueryKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanQueryKeys decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanQueryKeys
  rw [AlignedUnaryListClosure.added_length,
    directSourceFinalFanQueryIdentityBases_length,
    directSourceFinalFanQueryRanks_length, min_self]

/-- Query keys are ordinary pointwise sums of the repeated identity bases and
the selected finite ranks. -/
theorem directSourceFinalFanQueryKeys_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalFanQueryKeys decider symbols =
      List.zipWith (· + ·)
        (directSourceFinalFanQueryIdentityBases decider symbols)
        (directSourceFinalFanQueryRanks decider symbols) := by
  unfold directSourceFinalFanQueryKeys AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [directSourceFinalFanQueryIdentityBases_length,
      directSourceFinalFanQueryRanks_length])

noncomputable def
    directSourceFinalFanQueryIdentityBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanQueryIdentityBases decider) := by
  unfold directSourceFinalFanQueryIdentityBases
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalScaledAtomIdentityCodesComputableInPolyTime decider)
    (UnaryFieldFixedCopies.computableInPolyTime 3)

noncomputable def directSourceFinalFanQueryRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanQueryRanks decider) := by
  unfold directSourceFinalFanQueryRanks
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceCountPredsComputableInPolyTime decider)
    FinalFanQueryRanks.computableInPolyTime

/-- The three complete fan query keys per final occurrence are
polynomial-time computable, including for the empty source alphabet. -/
noncomputable def directSourceFinalFanQueryKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanQueryKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalFanQueryKeys
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalFanQueryIdentityBases decider)
      (directSourceFinalFanQueryRanks decider)
      (fun symbols => by
        rw [directSourceFinalFanQueryIdentityBases_length,
          directSourceFinalFanQueryRanks_length])
      (directSourceFinalFanQueryIdentityBasesComputableInPolyTime decider)
      (directSourceFinalFanQueryRanksComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end PeriodicCNFStripReduction
end LeanTrominoes

end

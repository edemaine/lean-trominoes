/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.UnaryAlignedAddSemantics
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldThreeSlotRankCompiler

/-! # Three consecutive block ordinals per unary index -/

noncomputable section

namespace LeanTrominoes.UnaryFieldThreeBlockOrdinals

open Computability Turing

/-- Three repeated bases `3 * index` per source index. -/
def bases (source : List Nat) : List Nat :=
  UnaryFieldFixedCopies.values 3
    (UnaryFieldConstantScale.values 3 source)

/-- Consecutive red/green/blue block ordinals for every source index. -/
def values (source : List Nat) : List Nat :=
  AlignedUnaryListClosure.added
    (bases source) (UnaryFieldThreeSlotRanks.values source)

@[simp] theorem bases_length (source : List Nat) :
    (bases source).length = 3 * source.length := by
  unfold bases UnaryFieldFixedCopies.values
    UnaryFieldConstantScale.values
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [List.map_cons, List.flatMap_cons, List.length_append,
        List.length_replicate, induction, List.length_cons]
      omega

@[simp] theorem slotRanks_length (source : List Nat) :
    (UnaryFieldThreeSlotRanks.values source).length = 3 * source.length := by
  simp [UnaryFieldThreeSlotRanks.values, Nat.mul_comm]

private theorem zipWith_bases_slotRanks (source : List Nat) :
    List.zipWith (· + ·) (bases source)
        (UnaryFieldThreeSlotRanks.values source) =
      source.flatMap fun index =>
        [3 * index, 3 * index + 1, 3 * index + 2] := by
  induction source with
  | nil => rfl
  | cons index source induction =>
      change List.zipWith (· + ·)
          ([index * 3, index * 3, index * 3] ++ bases source)
          ([0, 1, 2] ++ UnaryFieldThreeSlotRanks.values source) = _
      rw [List.zipWith_append (by simp), induction]
      simp [Nat.mul_comm]

/-- The arithmetic pipeline has the direct three-consecutive-ordinals
semantics. -/
theorem values_eq_flatMap (source : List Nat) :
    values source = source.flatMap fun index =>
      [3 * index, 3 * index + 1, 3 * index + 2] := by
  unfold values AlignedUnaryListClosure.added
  have valid : UnaryAlignedAddMachine.Valid (bases source)
      (UnaryFieldThreeSlotRanks.values source) :=
    UnaryAlignedAddMachine.Valid.of_length_eq (by
      rw [bases_length, slotRanks_length])
  rw [UnaryAlignedAddMachine.sums_eq_zipWith valid]
  exact zipWith_bases_slotRanks source

/-- Expanding compiled unary indices into three consecutive block ordinals
preserves polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields values := by
  let scaled := UnaryFieldConstantScale.computableInPolyTime 3
  let baseCompiler := TM2CompositionMachine.computableInPolyTime
    scaled (UnaryFieldFixedCopies.computableInPolyTime 3)
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields bases
    UnaryFieldThreeSlotRanks.values
    (fun source => by rw [bases_length, slotRanks_length])
    baseCompiler UnaryFieldThreeSlotRanks.computableInPolyTime

end LeanTrominoes.UnaryFieldThreeBlockOrdinals

end

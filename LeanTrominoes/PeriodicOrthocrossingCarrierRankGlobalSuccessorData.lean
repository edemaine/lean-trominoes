/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessMachine
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowCompiler
import LeanTrominoes.UnaryAlignedAddSemantics
import LeanTrominoes.UnaryExactOneBooleanCompiler
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Compiled global-rank successor bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobalSuccessor

abbrev InputEncoding := CarrierRankGlobal.InputEncoding

private theorem sum_map_constant {Value : Type*}
    (values : List Value) (constant : Nat) :
    (values.map fun _ => constant).sum = values.length * constant := by
  induction values with
  | nil => simp
  | cons value values induction =>
      rw [List.map_cons, List.sum_cons, induction, List.length_cons,
        Nat.succ_mul]
      omega

/-- Row-major ordered pairs of length-coded global unary ranks. -/
def rankWordPairs (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (UnaryFieldBinaryWords.words (CarrierRankGlobal.ranks descriptors))

/-- For every ordered datum pair, the truncated unary difference
`secondRank - firstRank`. -/
def rankExcesses (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses false
    (rankWordPairs descriptors)

/-- The row-major Boolean square selecting exactly rank-successor pairs. -/
def successorBits (descriptors : List RouteDescriptor) : List Bool :=
  UnaryExactOneBooleans.bits (rankExcesses descriptors)

/-- Same-key global-rank successors, the exact indexed carrier adjacency
predicate later used to select endpoint metadata. -/
def bits (descriptors : List RouteDescriptor) : List Bool :=
  List.zipWith (fun sameKey successor => sameKey && successor)
    (CarrierRankKeyEquality.bits descriptors)
    (successorBits descriptors)

@[simp] theorem ranks_length (descriptors : List RouteDescriptor) :
    (CarrierRankGlobal.ranks descriptors).length =
      CarrierRankKeyEqualityRows.side descriptors := by
  unfold CarrierRankGlobal.ranks
  rw [UnaryAlignedAddMachine.sums_length
    (CarrierRankGlobalValidity.valid descriptors)]
  rw [CarrierRankKeyBlockStarts.starts_length,
    CarrierRankCompiledKey.values_length]
  rfl

@[simp] theorem successorBits_length (descriptors : List RouteDescriptor) :
    (successorBits descriptors).length =
      CarrierRankKeyEqualityRows.side descriptors ^ 2 := by
  unfold successorBits rankExcesses rankWordPairs
  rw [UnaryExactOneBooleans.bits_length]
  simp [DelimitedBinaryWordPairExcessMachine.excesses,
    DelimitedBinaryWordPairProductMachine.pairs,
    UnaryFieldBinaryWords.words, pow_two]
  change ((CarrierRankGlobal.ranks descriptors).map fun _ =>
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length).sum =
    (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length *
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length
  rw [sum_map_constant, ranks_length]
  unfold CarrierRankKeyEqualityRows.side
  rfl

@[simp] theorem bits_length (descriptors : List RouteDescriptor) :
    (bits descriptors).length =
      CarrierRankKeyEqualityRows.side descriptors ^ 2 := by
  unfold bits
  rw [List.length_zipWith, CarrierRankKeyEqualityRows.bits_length,
    successorBits_length, min_self]

end CarrierRankGlobalSuccessor
end LeanTrominoes.PeriodicOrthocrossing

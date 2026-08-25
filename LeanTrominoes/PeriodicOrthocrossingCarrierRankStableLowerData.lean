/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsEncoding
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderEqualityCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderStrictLowerCompiler
import LeanTrominoes.UnaryAlignedAddValidity

/-! # Stable lower ranks within carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

abbrev InputEncoding := CarrierRankKeyEquality.InputEncoding

def intersection (first second : List Bool) : List Bool :=
  List.zipWith (· && ·) first second

/-- Strictly lower coordinates belonging to the same carrier key. -/
def lowerBits (descriptors : List RouteDescriptor) : List Bool :=
  intersection (CarrierRankKeyEquality.bits descriptors)
    (CarrierRankOrderStrictLower.bits descriptors)

/-- Equal coordinates belonging to the same carrier key.  Prefix counting
will retain exactly the earlier presentation ties. -/
def tieBits (descriptors : List RouteDescriptor) : List Bool :=
  intersection (CarrierRankKeyEquality.bits descriptors)
    (CarrierRankOrderEquality.bits descriptors)

def side (descriptors : List RouteDescriptor) : Nat :=
  (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length

@[simp] theorem keyBits_length (descriptors : List RouteDescriptor) :
    (CarrierRankKeyEquality.bits descriptors).length =
      side descriptors ^ 2 := by
  simp [CarrierRankKeyEquality.bits,
    CarrierRankKeyEquality.indexBits,
    CarrierRankKeyEquality.translationBits,
    CarrierRankKeyEquality.combined, side]

@[simp] theorem strictLowerBits_length
    (descriptors : List RouteDescriptor) :
    (CarrierRankOrderStrictLower.bits descriptors).length =
      side descriptors ^ 2 := by
  unfold CarrierRankOrderStrictLower.bits
  rw [SignedUnaryStrictLower.strictLowerBits_length
    (CarrierRankOrderStrictLower.polarity_lengths_eq descriptors)]
  rw [CarrierRankOrderField.values_length_eq_keyValues
    true .route descriptors]
  simp [side]

@[simp] theorem orderEqualityBits_length
    (descriptors : List RouteDescriptor) :
    (CarrierRankOrderEquality.bits descriptors).length =
      side descriptors ^ 2 := by
  unfold CarrierRankOrderEquality.bits
  rw [SignedUnaryEquality.equalityBits_length
    (CarrierRankOrderStrictLower.polarity_lengths_eq descriptors)]
  rw [CarrierRankOrderField.values_length_eq_keyValues
    true .route descriptors]
  simp [side]

@[simp] theorem lowerBits_length (descriptors : List RouteDescriptor) :
    (lowerBits descriptors).length = side descriptors ^ 2 := by
  simp [lowerBits, intersection]

@[simp] theorem tieBits_length (descriptors : List RouteDescriptor) :
    (tieBits descriptors).length = side descriptors ^ 2 := by
  simp [tieBits, intersection]

def lowerSquareInput (descriptors : List RouteDescriptor) :
    BoolSquareRows.Input where
  bits := lowerBits descriptors
  square := by
    rw [lowerBits_length, Nat.sqrt_eq']

def tieSquareInput (descriptors : List RouteDescriptor) :
    BoolSquareRows.Input where
  bits := tieBits descriptors
  square := by
    rw [tieBits_length, Nat.sqrt_eq']

@[simp] theorem lowerSquareInput_side (descriptors : List RouteDescriptor) :
    (lowerSquareInput descriptors).side = side descriptors := by
  unfold BoolSquareRows.Input.side lowerSquareInput
  rw [lowerBits_length, Nat.sqrt_eq']

@[simp] theorem tieSquareInput_side (descriptors : List RouteDescriptor) :
    (tieSquareInput descriptors).side = side descriptors := by
  unfold BoolSquareRows.Input.side tieSquareInput
  rw [tieBits_length, Nat.sqrt_eq']

def lowerRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨(List.replicate (side descriptors) (side descriptors)).splitLengths
    (lowerBits descriptors)⟩

def tieRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨(List.replicate (side descriptors) (side descriptors)).splitLengths
    (tieBits descriptors)⟩

theorem lowerSquareInput_delimitedRows (descriptors : List RouteDescriptor) :
    (lowerSquareInput descriptors).delimitedRows = lowerRows descriptors := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold BoolSquareRows.Input.rows BoolSquareRows.Input.sizes
  rw [lowerSquareInput_side]
  simp only [lowerSquareInput]

theorem tieSquareInput_delimitedRows (descriptors : List RouteDescriptor) :
    (tieSquareInput descriptors).delimitedRows = tieRows descriptors := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold BoolSquareRows.Input.rows BoolSquareRows.Input.sizes
  rw [tieSquareInput_side]
  simp only [tieSquareInput]

def lowerCounts (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts (lowerRows descriptors)

def tieCounts (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts (tieRows descriptors)

@[simp] theorem lowerCounts_length (descriptors : List RouteDescriptor) :
    (lowerCounts descriptors).length = side descriptors := by
  unfold lowerCounts
  rw [← lowerSquareInput_delimitedRows]
  unfold DelimitedBinaryWordTrueCounts.counts
    BoolSquareRows.Input.delimitedRows
  rw [List.length_map, BoolSquareRows.rows_length,
    lowerSquareInput_side]

@[simp] theorem tieCounts_length (descriptors : List RouteDescriptor) :
    (tieCounts descriptors).length = side descriptors := by
  unfold tieCounts
  rw [← tieSquareInput_delimitedRows]
  unfold BoolSquareRows.Input.delimitedRows
  rw [DelimitedBinaryWordPrefixTrueCounts.counts_length,
    BoolSquareRows.rows_length, tieSquareInput_side]

/-- Stable lower rank of every compact datum within its own carrier key. -/
def ranks (descriptors : List RouteDescriptor) : List Nat :=
  UnaryAlignedAddMachine.sums
    (lowerCounts descriptors) (tieCounts descriptors)

def additionInput (descriptors : List RouteDescriptor) :
    UnaryAlignedAddMachine.Input where
  firsts := lowerCounts descriptors
  seconds := tieCounts descriptors
  valid := UnaryAlignedAddMachine.Valid.of_length_eq (by simp)

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

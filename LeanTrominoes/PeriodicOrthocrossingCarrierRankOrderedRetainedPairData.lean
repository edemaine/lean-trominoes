/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCrossoverData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNextSliceData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairOwnershipData
import LeanTrominoes.UnaryCarrierPairBitCompiler

/-! # Sparse retained pairs from the global carrier-rank matrix -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

/-- Candidate adjacent pairs after crossover suppression. -/
def nonCrossoverCandidateBits
    (descriptors : List RouteDescriptor) : List Bool :=
  combined (bits descriptors) (differentCrossoverBits descriptors)

/-- Exact retained zero-owner adjacent-pair mask. -/
def retainedMaskBits (descriptors : List RouteDescriptor) : List Bool :=
  combined
    (nonCrossoverCandidateBits descriptors)
    (representativeBits descriptors)

def retainedAxisBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (retainedMaskBits descriptors) (axisBits descriptors)

def retainedNextSliceBits
    (descriptors : List RouteDescriptor) : List Bool :=
  combined (retainedMaskBits descriptors) (nextSliceBits descriptors)

/-- Codes zero through two contribute mask and axis; zero or two contributes
the doubled next-slice bit. -/
def baseEmissionCodes (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (BooleanListUnaryFields.values (retainedMaskBits descriptors))
    (BooleanListUnaryFields.values (retainedAxisBits descriptors))

def doubledNextSliceCodes
    (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (BooleanListUnaryFields.values (retainedNextSliceBits descriptors))
    (BooleanListUnaryFields.values (retainedNextSliceBits descriptors))

/-- Zero suppresses a pair; codes one through four retain its two metadata
bits. -/
def emissionCodes (descriptors : List RouteDescriptor) : List Nat :=
  AlignedUnaryListClosure.added
    (baseEmissionCodes descriptors)
    (doubledNextSliceCodes descriptors)

/-- Exact sparse `(axis, nextSlice)` stream in global key-major adjacent-pair
order. -/
def retainedPairBits (descriptors : List RouteDescriptor) :
    List (Bool × Bool) :=
  UnaryCarrierPairBits.pairs (emissionCodes descriptors)

@[simp] theorem nonCrossoverCandidateBits_length
    (descriptors : List RouteDescriptor) :
    (nonCrossoverCandidateBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [nonCrossoverCandidateBits, combined]

@[simp] theorem retainedMaskBits_length
    (descriptors : List RouteDescriptor) :
    (retainedMaskBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [retainedMaskBits, combined]

@[simp] theorem retainedAxisBits_length
    (descriptors : List RouteDescriptor) :
    (retainedAxisBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [retainedAxisBits, combined, axisBits]

@[simp] theorem retainedNextSliceBits_length
    (descriptors : List RouteDescriptor) :
    (retainedNextSliceBits descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [retainedNextSliceBits, combined]

@[simp] theorem baseEmissionCodes_length
    (descriptors : List RouteDescriptor) :
    (baseEmissionCodes descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [baseEmissionCodes, BooleanListUnaryFields.values]

@[simp] theorem doubledNextSliceCodes_length
    (descriptors : List RouteDescriptor) :
    (doubledNextSliceCodes descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [doubledNextSliceCodes, BooleanListUnaryFields.values]

@[simp] theorem emissionCodes_length
    (descriptors : List RouteDescriptor) :
    (emissionCodes descriptors).length =
      (Field.rankOrderedValues .keyRoute descriptors).length ^ 2 := by
  simp [emissionCodes]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

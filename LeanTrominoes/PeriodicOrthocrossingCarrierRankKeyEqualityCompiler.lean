/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedWordCorrect
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldCompiler
import LeanTrominoes.SignedUnaryEqualityCompiler
import LeanTrominoes.UnaryFieldEqualityRowsCompiler

/-! # Compiler for equality of compact carrier-rank keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEquality

open Computability Turing

abbrev InputEncoding (descriptors : List RouteDescriptor) :=
  DelimitedBinaryWords.encode
    (RouteDescriptorBinaryWords.words descriptors)

def fieldBits (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) : List Bool :=
  UnaryFieldEqualityRows.equalityBits
    (CarrierRankKeyField.values field descriptors)

def horizontalBits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (CarrierRankKeyField.values .horizontalPositive descriptors)
    (CarrierRankKeyField.values .horizontalNegative descriptors)

def verticalBits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (CarrierRankKeyField.values .verticalPositive descriptors)
    (CarrierRankKeyField.values .verticalNegative descriptors)

def combined (first second : List Bool) : List Bool :=
  List.zipWith (· && ·) first second

def indexBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (fieldBits .route descriptors) (fieldBits .segment descriptors)

def translationBits (descriptors : List RouteDescriptor) : List Bool :=
  combined (horizontalBits descriptors) (verticalBits descriptors)

/-- Row-major bits marking pairs of compact rank data with equal carrier
keys. -/
def bits (descriptors : List RouteDescriptor) : List Bool :=
  combined (indexBits descriptors) (translationBits descriptors)

@[simp] theorem fieldValues_length
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (CarrierRankKeyField.values field descriptors).length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length := by
  simp [CarrierRankKeyField.values,
    CarrierSourceKeyRepresentativeLookup.values,
    LastTrueUnaryValueLookupMachine.lookups]

theorem fieldValues_lengths_eq
    (first second : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (CarrierRankKeyField.values first descriptors).length =
      (CarrierRankKeyField.values second descriptors).length := by
  simp

@[simp] theorem fieldBits_length
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (fieldBits field descriptors).length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length ^ 2 := by
  simp [fieldBits]

@[simp] theorem horizontalBits_length (descriptors : List RouteDescriptor) :
    (horizontalBits descriptors).length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length ^ 2 := by
  simp [horizontalBits]

@[simp] theorem verticalBits_length (descriptors : List RouteDescriptor) :
    (verticalBits descriptors).length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length ^ 2 := by
  simp [verticalBits]

noncomputable def fieldBitsComputableInPolyTime
    (field : CarrierKeyFieldProjector.Field)
    (wordCorrect : CarrierKeyFieldProjector.WordCorrect field) :
    TM2ComputableInPolyTime InputEncoding id (fieldBits field) :=
  UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
    InputEncoding (CarrierRankKeyField.values field)
    (CarrierRankKeyField.valuesComputableInPolyTime field wordCorrect)

noncomputable def horizontalBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id horizontalBits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    InputEncoding
    (CarrierRankKeyField.values .horizontalPositive)
    (CarrierRankKeyField.values .horizontalNegative)
    (fieldValues_lengths_eq .horizontalPositive .horizontalNegative)
    (CarrierRankKeyField.valuesComputableInPolyTime .horizontalPositive
      CarrierKeyFieldProjector.wordCorrect_horizontalPositive)
    (CarrierRankKeyField.valuesComputableInPolyTime .horizontalNegative
      CarrierKeyFieldProjector.wordCorrect_horizontalNegative)

noncomputable def verticalBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id verticalBits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    InputEncoding
    (CarrierRankKeyField.values .verticalPositive)
    (CarrierRankKeyField.values .verticalNegative)
    (fieldValues_lengths_eq .verticalPositive .verticalNegative)
    (CarrierRankKeyField.valuesComputableInPolyTime .verticalPositive
      CarrierKeyFieldProjector.wordCorrect_verticalPositive)
    (CarrierRankKeyField.valuesComputableInPolyTime .verticalNegative
      CarrierKeyFieldProjector.wordCorrect_verticalNegative)

noncomputable def indexBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id indexBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    (fieldBits .route) (fieldBits .segment)
    (fun descriptors => by simp)
    (fieldBitsComputableInPolyTime .route
      CarrierKeyFieldProjector.wordCorrect_route)
    (fieldBitsComputableInPolyTime .segment
      CarrierKeyFieldProjector.wordCorrect_segment)

noncomputable def translationBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id translationBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction horizontalBits verticalBits
    (fun descriptors => by simp)
    horizontalBitsComputableInPolyTime verticalBitsComputableInPolyTime

/-- Equality of every ordered pair of compact carrier-rank keys is
computable in polynomial time. -/
noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id bits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction indexBits translationBits
    (fun descriptors => by simp [indexBits, translationBits, combined])
    indexBitsComputableInPolyTime translationBitsComputableInPolyTime

end CarrierRankKeyEquality
end LeanTrominoes.PeriodicOrthocrossing

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNextSliceData
import LeanTrominoes.SignedUnarySuccessorCompiler

/-! # Compiler for next-slice bits of rank-ordered carrier pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing
open CarrierRankDatumCompiledFields

noncomputable def horizontalNextBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id horizontalNextBits :=
  SignedUnarySuccessor.bitsComputableInPolyTime
    InputEncoding
    (Field.rankOrderedValues .normalizationHorizontalPositive)
    (Field.rankOrderedValues .normalizationHorizontalNegative)
    (rankOrderedValues_lengths_eq _ _)
    (Field.rankOrderedValuesComputableInPolyTime
      .normalizationHorizontalPositive)
    (Field.rankOrderedValuesComputableInPolyTime
      .normalizationHorizontalNegative)

noncomputable def verticalSameBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id verticalSameBits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    InputEncoding
    (Field.rankOrderedValues .normalizationVerticalPositive)
    (Field.rankOrderedValues .normalizationVerticalNegative)
    (rankOrderedValues_lengths_eq _ _)
    (Field.rankOrderedValuesComputableInPolyTime
      .normalizationVerticalPositive)
    (Field.rankOrderedValuesComputableInPolyTime
      .normalizationVerticalNegative)

/-- Exact next-slice bits for every rank-ordered carrier pair are
polynomial-time computable. -/
noncomputable def nextSliceBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id nextSliceBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction horizontalNextBits verticalSameBits
    (fun descriptors => by simp)
    horizontalNextBitsComputableInPolyTime
    verticalSameBitsComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end

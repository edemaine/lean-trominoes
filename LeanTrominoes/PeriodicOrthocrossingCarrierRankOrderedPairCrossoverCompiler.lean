/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCrossoverData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCompiler

/-! # Compiler for crossover tests on rank-ordered carrier pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing
open CarrierRankDatumCompiledFields

noncomputable def fieldEqualityConjunctionComputableInPolyTime
    (field : Field) (rest : List Field) :
    TM2ComputableInPolyTime InputEncoding id
      (fieldEqualityConjunction field rest) := by
  induction rest generalizing field with
  | nil => exact fieldEqualityBitsComputableInPolyTime field
  | cons next rest induction =>
      exact AlignedBooleanListClosure.combinedComputableInPolyTime
        InputEncoding .conjunction
        (fieldEqualityBits field)
        (fieldEqualityConjunction next rest)
        (fun descriptors => by simp)
        (fieldEqualityBitsComputableInPolyTime field)
        (induction next)

noncomputable def crossingPayloadEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id
      crossingPayloadEqualityBits :=
  fieldEqualityConjunctionComputableInPolyTime
    .crossingFirstRoute crossingPayloadTail

noncomputable def sameCrossoverBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id sameCrossoverBits := by
  let bothBoundariesCompiler :=
    AlignedBooleanListClosure.combinedComputableInPolyTime
      InputEncoding .conjunction firstBoundaryBits secondBoundaryBits
      (fun descriptors => by
        simp [firstBoundaryBits, secondBoundaryBits])
      firstBoundaryBitsComputableInPolyTime
      secondBoundaryBitsComputableInPolyTime
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    (fun descriptors => combined
      (firstBoundaryBits descriptors) (secondBoundaryBits descriptors))
    crossingPayloadEqualityBits
    (fun descriptors => by
      simp [combined, firstBoundaryBits, secondBoundaryBits])
    bothBoundariesCompiler crossingPayloadEqualityBitsComputableInPolyTime

noncomputable def differentCrossoverBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id differentCrossoverBits :=
  AlignedBooleanListClosure.mapNegatedComputableInPolyTime
    InputEncoding sameCrossoverBits sameCrossoverBitsComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end

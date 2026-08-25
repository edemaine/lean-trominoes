/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerData

/-! # Compiler for stable carrier-rank comparison bits -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

opaque lowerBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id lowerBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    CarrierRankKeyEquality.bits CarrierRankOrderStrictLower.bits
    (fun descriptors => by simp)
    CarrierRankKeyEquality.bitsComputableInPolyTime
    CarrierRankOrderStrictLower.bitsComputableInPolyTime

opaque tieBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id tieBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    CarrierRankKeyEquality.bits CarrierRankOrderEquality.bits
    (fun descriptors => by simp)
    CarrierRankKeyEquality.bitsComputableInPolyTime
    CarrierRankOrderEquality.bitsComputableInPolyTime

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end

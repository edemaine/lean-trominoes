/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderStrictLowerCompiler
import LeanTrominoes.SignedUnaryEqualityCompiler

/-! # Compiler for carrier-rank order-coordinate equality -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderEquality

open Computability Turing

/-- Row-major equality bits for compact carrier-rank order coordinates. -/
def bits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryEquality.equalityBits
    (CarrierRankOrderField.values true descriptors)
    (CarrierRankOrderField.values false descriptors)

noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id bits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    (CarrierRankOrderField.values true)
    (CarrierRankOrderField.values false)
    CarrierRankOrderStrictLower.polarity_lengths_eq
    (CarrierRankOrderField.valuesComputableInPolyTime true)
    (CarrierRankOrderField.valuesComputableInPolyTime false)

end CarrierRankOrderEquality
end LeanTrominoes.PeriodicOrthocrossing

end

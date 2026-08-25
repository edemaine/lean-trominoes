/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldCompiler
import LeanTrominoes.SignedUnaryStrictLowerCompiler

/-! # Compiler for strict order-coordinate comparisons of carrier rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderStrictLower

open Computability Turing

/-- Row-major strict-lower comparison bits for the compact carrier-rank
order-coordinate fields. -/
def bits (descriptors : List RouteDescriptor) : List Bool :=
  SignedUnaryStrictLower.strictLowerBits
    (CarrierRankOrderField.values true descriptors)
    (CarrierRankOrderField.values false descriptors)

theorem polarity_lengths_eq (descriptors : List RouteDescriptor) :
    (CarrierRankOrderField.values true descriptors).length =
      (CarrierRankOrderField.values false descriptors).length := by
  simp [CarrierRankOrderField.values,
    CarrierOrderRepresentativeLookup.values,
    LastTrueUnaryValueLookupMachine.lookups]

/-- Strict comparison of every ordered pair of compact carrier-rank order
coordinates is computable in polynomial time. -/
noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id bits :=
  SignedUnaryStrictLower.strictLowerBitsComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    (CarrierRankOrderField.values true)
    (CarrierRankOrderField.values false)
    polarity_lengths_eq
    (CarrierRankOrderField.valuesComputableInPolyTime true)
    (CarrierRankOrderField.valuesComputableInPolyTime false)

end CarrierRankOrderStrictLower
end LeanTrominoes.PeriodicOrthocrossing

end

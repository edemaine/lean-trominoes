/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerBitCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler preparation of stable carrier-rank square matrices -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

noncomputable def lowerSquareInputComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      BoolSquareRows.finEncoding.encode lowerSquareInput :=
  @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (List RouteDescriptor) (List Bool) BoolSquareRows.Input
    DelimitedBinaryWords.Token Bool InputEncoding id
    BoolSquareRows.finEncoding.encode lowerBits lowerSquareInput
    lowerBitsComputableInPolyTime (fun input => by
      rw [BoolSquareRows.finEncoding_encode_eq_bits]
      simp only [lowerSquareInput, id_eq])

noncomputable def tieSquareInputComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      BoolSquareRows.finEncoding.encode tieSquareInput :=
  @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (List RouteDescriptor) (List Bool) BoolSquareRows.Input
    DelimitedBinaryWords.Token Bool InputEncoding id
    BoolSquareRows.finEncoding.encode tieBits tieSquareInput
    tieBitsComputableInPolyTime (fun input => by
      rw [BoolSquareRows.finEncoding_encode_eq_bits]
      simp only [tieSquareInput, id_eq])

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end

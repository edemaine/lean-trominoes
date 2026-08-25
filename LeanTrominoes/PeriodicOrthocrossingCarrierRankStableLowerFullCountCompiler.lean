/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerSquareCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for strict-lower same-carrier row counts -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

opaque lowerCountsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields lowerCounts := by
  let rowCompiler := TM2CompositionMachine.computableInPolyTime
    lowerSquareInputComputableInPolyTime
    BoolSquareRowsMachine.computableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime rowCompiler
    DelimitedBinaryWordTrueCounts.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := lowerCounts) counted (fun descriptors => by
      unfold lowerCounts
      rw [lowerSquareInput_delimitedRows])

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end

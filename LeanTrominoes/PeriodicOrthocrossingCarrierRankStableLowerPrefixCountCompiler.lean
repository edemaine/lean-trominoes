/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerSquareCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for equal-coordinate presentation-prefix counts -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

open Computability Turing

opaque tieCountsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields tieCounts := by
  let rowCompiler := TM2CompositionMachine.computableInPolyTime
    tieSquareInputComputableInPolyTime
    BoolSquareRowsMachine.computableInPolyTime
  let counted := TM2CompositionMachine.computableInPolyTime rowCompiler
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := tieCounts) counted (fun _ => rfl)

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing

end

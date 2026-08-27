/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanCompiler

/-! # Tape-level axis-tagged retained carrier-span streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

/-- Reinterpret the tagged natural fields at their already-emitted unary
tape representation, ready for a symbol-stream postprocessor. -/
noncomputable def taggedSpanStreamComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id taggedSpanStream where
  tm := taggedSpanCodesComputableInPolyTime.tm
  inputAlphabet := taggedSpanCodesComputableInPolyTime.inputAlphabet
  outputAlphabet := taggedSpanCodesComputableInPolyTime.outputAlphabet
  time := taggedSpanCodesComputableInPolyTime.time
  outputsFun descriptors := by
    simpa [taggedSpanStream] using
      taggedSpanCodesComputableInPolyTime.outputsFun descriptors

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanCompiler

/-! # Tape-level packed retained carrier-span streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

/-- Reinterpret the packed natural fields at their emitted unary tape
representation for the symbol-stream decoder. -/
noncomputable def packedSpanStreamComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id packedSpanStream where
  tm := packedSpanCodesComputableInPolyTime.tm
  inputAlphabet := packedSpanCodesComputableInPolyTime.inputAlphabet
  outputAlphabet := packedSpanCodesComputableInPolyTime.outputAlphabet
  time := packedSpanCodesComputableInPolyTime.time
  outputsFun descriptors := by
    simpa [packedSpanStream] using
      packedSpanCodesComputableInPolyTime.outputsFun descriptors

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end

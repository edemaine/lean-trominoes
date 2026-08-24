/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Complete merged carrier source-key stream compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

open Computability Turing

def tokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPairMerge.tokens
    (CarrierSourceKeyComponentStream.tokens input)

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      tokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => DelimitedBinaryWordGuardedPairMerge.tokens
      (CarrierSourceKeyComponentStream.tokens input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyComponentStream.tokensComputableInPolyTime
    DelimitedBinaryWordGuardedPairMerge.tokensComputableInPolyTime

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing

end

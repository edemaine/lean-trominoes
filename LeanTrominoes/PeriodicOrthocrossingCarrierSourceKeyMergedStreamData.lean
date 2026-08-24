/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData

/-! # Complete merged carrier source-key stream data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

def tokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPairMerge.tokens
    (CarrierSourceKeyComponentStream.tokens input)

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordGuardedStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierKeyCompactAtomWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Pair-stream compiler for exact compact bend atom words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendCompactAtomWordStream

open Computability Turing

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  GuardedCarrierKeyCompactAtomWords.tokens
    (BendCompactAtomWordGuardedStream.emittedStream tokens)

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream := by
  change TM2ComputableInPolyTime id id
    (fun tokens => GuardedCarrierKeyCompactAtomWords.tokens
      (BendCompactAtomWordGuardedStream.emittedStream tokens))
  exact TM2CompositionMachine.computableInPolyTime
    BendCompactAtomWordGuardedStream.emittedStreamComputableInPolyTime
    GuardedCarrierKeyCompactAtomWords.tokensComputableInPolyTime

end BendCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanStreamCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Tagged.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoder

/-! # Compiler for rank-ordered retained carrier route directions -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

/-- The complete retained carrier direction stream is polynomial-time
computable from the numeric route descriptors. -/
noncomputable def retainedRouteDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id
      retainedRouteDirectionStream := by
  change TM2ComputableInPolyTime InputEncoding id
    (fun descriptors => CarrierTaggedSpanRouteDirections.stream
      (taggedSpanStream descriptors))
  exact TM2CompositionMachine.computableInPolyTime
    taggedSpanStreamComputableInPolyTime
    CarrierTaggedSpanRouteDirections.streamComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end

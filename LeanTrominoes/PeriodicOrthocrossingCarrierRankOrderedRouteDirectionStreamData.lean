/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderData

/-! # Rank-ordered retained carrier route-direction streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- Compile the sparse rank-ordered tagged spans into route-delimited
directions.  Rejected matrix entries remain zero fields and emit nothing. -/
def retainedRouteDirectionStream (descriptors : List RouteDescriptor) :
    List CarrierSpanRouteDirections.Token :=
  CarrierTaggedSpanRouteDirections.stream
    (taggedSpanStream descriptors)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

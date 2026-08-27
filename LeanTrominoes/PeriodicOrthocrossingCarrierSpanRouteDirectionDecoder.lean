/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Decoding retained carrier spans into complete route words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSpanRouteDirections

open Computability Turing
noncomputable def blockOutputComputableInPolyTime (horizontal : Bool) :
    TM2ComputableInPolyTime id id (blockOutput horizontal) := by
  exact TM2ListAppend.computableInPolyTime
    (FiniteStateTransducer.computableInPolyTime
      Control.zero (firstTransition horizontal) finish)
    (FiniteStateTransducer.computableInPolyTime
      Control.zero (lastTransition horizontal) finish)

noncomputable def streamComputableInPolyTime (horizontal : Bool) :
    TM2ComputableInPolyTime id id (stream horizontal) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (blockOutputComputableInPolyTime horizontal) isFieldEnd

end CarrierSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing

end

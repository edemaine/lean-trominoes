/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Slot-pair-stream compiler for padded crossing carrier-key axes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingCarrierKeyAxisStream

open Computability Turing

def emittedFields
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisCompiledFields
    tokens

noncomputable def emittedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedFields := by
  exact TM2EndDelimitedBlockMap.computableInPolyTime
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisCompiledFieldsComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CrossingCarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagFintypeData

/-! # Compiler for batched occurrence-slot guards -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing
namespace SlotGuardBatch

open Computability Turing

/-- Any fixed list of two-slot guards is evaluated by one finite-state scan. -/
noncomputable def truthValuesComputableInPolyTime (slots : List Slot) :
    TM2ComputableInPolyTime id id (truthValues slots) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output initial transition (finish slots))
  exact FiniteStateTransducer.computableInPolyTime
    initial transition (finish slots)

/-- The complete crossing-aligned slot-guard word is polynomial-time. -/
noncomputable def crossingTruthValuesComputableInPolyTime :
    TM2ComputableInPolyTime id id crossingTruthValues := by
  change TM2ComputableInPolyTime id id (truthValues crossingSlots)
  exact truthValuesComputableInPolyTime crossingSlots

end SlotGuardBatch
end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end

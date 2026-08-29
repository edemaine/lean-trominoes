/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # Compiler grouping final occurrence roles and slots by copied clause -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open Computability Turing

/-- One finite-state pass groups canonical one-to-three occurrence blocks
into the slot-tuple inputs expected by the Figure 9 route-record compiler. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id slotInputs := by
  unfold slotInputs
  exact FiniteStateTransducer.computableInPolyTime none transition finish

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceFrameDecoder

/-! # Mixed-radix arithmetic for complete final occurrence frames -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

theorem DirectFinalOccurrenceFrame.codeOfData_eq_role_slot
    (frame : DirectFinalOccurrenceFrame.Data) :
    DirectFinalOccurrenceFrame.codeOfData frame =
      8 * (DirectFinalOccurrenceFrame.roleIndex
        frame.variableFan frame.clauseFrame).val +
        (DirectFinalOccurrenceFrame.boundedSlot
          frame.occurrenceSlot).val := by
  unfold DirectFinalOccurrenceFrame.codeOfData
    DirectFinalOccurrenceFrame.variableFanBase
    DirectFinalOccurrenceFrame.clauseFrameBase
    DirectFinalOccurrenceFrame.occurrenceSlotValue
    DirectFinalOccurrenceFrame.roleIndex
    DirectFinalOccurrenceFrame.boundedSlot
  rw [FiniteIndexSlotUnaryDecoder.pairIndex_val]
  ring

end LeanTrominoes.PeriodicCNFStripReduction

end

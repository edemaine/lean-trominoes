/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceFrameCodeArithmetic

/-! # Exact decoding semantics for complete final occurrence frames -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Decoding an exact mixed-radix code recovers all three finite frame fields. -/
theorem DirectFinalOccurrenceFrame.dataOfPair_decode_codeOfData
    (frame : DirectFinalOccurrenceFrame.Data) :
    DirectFinalOccurrenceFrame.dataOfPair
        (FiniteIndexSlotUnaryDecoder.boundedCode
          (Fintype.card DirectFinalOccurrenceFrame.VariableFan *
            Fintype.card DirectFinalOccurrenceFrame.ClauseFrame)
          (DirectFinalOccurrenceFrame.codeOfData frame)) =
      frame := by
  rw [DirectFinalOccurrenceFrame.codeOfData_eq_role_slot]
  rw [FiniteIndexSlotUnaryDecoder.boundedCode_index_slot]
  unfold DirectFinalOccurrenceFrame.dataOfPair
    DirectFinalOccurrenceFrame.decodedRolePair
    DirectFinalOccurrenceFrame.roleIndex
    DirectFinalOccurrenceFrame.boundedSlot
  rw [FiniteIndexSlotUnaryDecoder.unpairIndex_pairIndex]
  simp only [Equiv.symm_apply_apply]
  cases frame
  rename_i fan slot clauseFrame
  cases slot <;> rfl

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteEncodingNativeFields
import LeanTrominoes.FiniteRoleSlotUnaryDecoderArithmetic
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotDecoderData

/-! # Correctness of final occurrence-role/slot decoding -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotDecoder

/-- The reserved eight-value block encoding decodes an actual final
occurrence role and slot without loss. -/
theorem decode_role_slot (role : Role) (slot : Slot) :
    FiniteRoleSlotUnaryDecoder.decode
        (FiniteRoleSlotUnaryDecoder.boundedCode
          (8 * FiniteEncodingNativeFields.symbolIndex role + slot.val)) =
      (role, slot) := by
  simpa only [FiniteEncodingNativeFields.symbolIndex] using
    (FiniteRoleSlotUnaryDecoder.decode_role_slot_index role slot)

end LeanTrominoes.FinalOccurrenceRoleSlotDecoder

end

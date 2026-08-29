/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotDecoderSemantics
import LeanTrominoes.UnaryAlignedAddMachine

/-! # List correctness of final occurrence-role/slot decoding -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotDecoder

/-- Aligned unary addition of role-block bases and slot values decodes
pointwise to the original role/slot pairs. -/
theorem pairs_sums_roleBases_slotValues
    (roles : List Role) (slots : List Slot)
    (lengthEq : roles.length = slots.length) :
    pairs
        (UnaryAlignedAddMachine.sums
          (roles.map fun role =>
            8 * FiniteEncodingNativeFields.symbolIndex role)
          (slots.map Fin.val)) =
      List.zip roles slots := by
  induction roles generalizing slots with
  | nil =>
      cases slots with
      | nil => rfl
      | cons slot slots => simp at lengthEq
  | cons role roles induction =>
      cases slots with
      | nil => simp at lengthEq
      | cons slot slots =>
          have tailLength : roles.length = slots.length := by
            simpa using lengthEq
          simp only [List.map_cons, UnaryAlignedAddMachine.sums,
            pairs, FiniteRoleSlotUnaryDecoder.pairs, List.zip_cons_cons]
          rw [decode_role_slot]
          exact congrArg (List.cons (role, slot))
            (induction slots tailLength)

end LeanTrominoes.FinalOccurrenceRoleSlotDecoder

end

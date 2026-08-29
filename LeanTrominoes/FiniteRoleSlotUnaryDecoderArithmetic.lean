/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderData

/-! # Arithmetic correctness of generic unary role/slot decoding -/

noncomputable section

namespace LeanTrominoes.FiniteRoleSlotUnaryDecoder

variable {Role : Type} [Fintype Role] [Nonempty Role]

@[simp] theorem advance_zero (control : Control Role) :
    advance control 0 = control :=
  rfl

theorem advance_succ (control : Control Role) (steps : Nat) :
    advance control (Nat.succ steps) = advance (increment control) steps :=
  rfl

theorem controlCode_boundedCode (code : Nat) :
    controlCode (boundedCode (Role := Role) code) =
      min code (roleCodeBound Role - 1) := by
  unfold controlCode boundedCode
  dsimp only
  have modLt :
      min code (roleCodeBound Role - 1) % 8 < 8 :=
    Nat.mod_lt _ (by omega)
  omega

private theorem boundedCode_congr {first second : Nat}
    (equal :
      min first (roleCodeBound Role - 1) =
        min second (roleCodeBound Role - 1)) :
    boundedCode (Role := Role) first = boundedCode second := by
  apply Prod.ext
  · apply Fin.ext
    simp only [boundedCode, Fin.val_mk]
    exact congrArg (fun value => value / 8) equal
  · apply Fin.ext
    simp only [boundedCode, Fin.val_mk]
    exact congrArg (fun value => value % 8) equal

theorem increment_boundedCode (code : Nat) :
    increment (boundedCode (Role := Role) code) =
      boundedCode (code + 1) := by
  unfold increment
  rw [controlCode_boundedCode]
  apply boundedCode_congr
  have boundPos := roleCodeBound_pos Role
  omega

theorem advance_boundedCode (code steps : Nat) :
    advance (boundedCode (Role := Role) code) steps =
      boundedCode (code + steps) := by
  induction steps generalizing code with
  | zero => rfl
  | succ steps induction =>
      rw [advance_succ, increment_boundedCode, induction]
      congr 1
      omega

/-- A valid eight-value block code recovers its role and slot. -/
theorem decode_role_slot_index (role : Role) (slot : Slot) :
    decode (boundedCode (Role := Role)
        (8 * (Fintype.equivFin Role role).val + slot.val)) =
      (role, slot) := by
  have roleLt := (Fintype.equivFin Role role).isLt
  have slotLt := slot.isLt
  have codeLt :
      8 * (Fintype.equivFin Role role).val + slot.val <
        roleCodeBound Role := by
    rw [roleCodeBound_eq]
    omega
  unfold decode
  have boundedEq :
      min (8 * (Fintype.equivFin Role role).val + slot.val)
          (roleCodeBound Role - 1) =
        8 * (Fintype.equivFin Role role).val + slot.val := by
    omega
  apply Prod.ext
  · change (Fintype.equivFin Role).symm
        (boundedCode
          (8 * (Fintype.equivFin Role role).val + slot.val)).1 = role
    have indexEq :
        (boundedCode
          (8 * (Fintype.equivFin Role role).val + slot.val)).1 =
          Fintype.equivFin Role role := by
      apply Fin.ext
      simp only [boundedCode, Fin.val_mk]
      omega
    calc
      _ = (Fintype.equivFin Role).symm
          (Fintype.equivFin Role role) :=
        congrArg (Fintype.equivFin Role).symm indexEq
      _ = role := (Fintype.equivFin Role).symm_apply_apply role
  · apply Fin.ext
    simp only [boundedCode, Fin.val_mk]
    omega

end LeanTrominoes.FiniteRoleSlotUnaryDecoder

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.EquivFin

/-! # Generic finite decoder for unary role/slot codes -/

noncomputable section

namespace LeanTrominoes.FiniteRoleSlotUnaryDecoder

abbrev Slot := Fin 8
abbrev Pair (Role : Type) := Role × Slot
abbrev Control (Role : Type) [Fintype Role] :=
  Fin (Fintype.card Role) × Slot
noncomputable def roleCodeBound (Role : Type) [Fintype Role] [Nonempty Role] : Nat :=
  8 * Fintype.card Role

theorem roleCodeBound_eq (Role : Type) [Fintype Role] [Nonempty Role] :
    roleCodeBound Role = 8 * Fintype.card Role :=
  rfl

theorem roleCodeBound_pos (Role : Type) [Fintype Role] [Nonempty Role] :
    0 < roleCodeBound Role := by
  rw [roleCodeBound_eq]
  have cardPos : 0 < Fintype.card Role := Fintype.card_pos
  omega

def boundedCode {Role : Type} [Fintype Role] [Nonempty Role]
    (code : Nat) : Control Role :=
  let bounded := min code (roleCodeBound Role - 1)
  let roleIndex : Fin (Fintype.card Role) :=
    ⟨bounded / 8, by
      have boundedLt : bounded < roleCodeBound Role := by
        have := roleCodeBound_pos Role
        dsimp only [bounded]
        omega
      rw [roleCodeBound_eq] at boundedLt
      omega⟩
  let slot : Slot := ⟨bounded % 8, Nat.mod_lt _ (by omega)⟩
  (roleIndex, slot)

def controlCode {Role : Type} [Fintype Role] [Nonempty Role]
    (control : Control Role) : Nat :=
  8 * control.1.val + control.2.val

def zero {Role : Type} [Fintype Role] [Nonempty Role] : Control Role :=
  boundedCode 0

def increment {Role : Type} [Fintype Role] [Nonempty Role]
    (control : Control Role) : Control Role :=
  boundedCode (controlCode control + 1)

def advance {Role : Type} [Fintype Role] [Nonempty Role] :
    Control Role → Nat → Control Role
  | control, 0 => control
  | control, Nat.succ steps => advance (increment control) steps

def decode {Role : Type} [Fintype Role] [Nonempty Role]
    (control : Control Role) : Pair Role :=
  ((Fintype.equivFin Role).symm control.1, control.2)

def pairs {Role : Type} [Fintype Role] [Nonempty Role]
    (codes : List Nat) : List (Pair Role) :=
  codes.map fun code => decode (boundedCode code)

end LeanTrominoes.FiniteRoleSlotUnaryDecoder

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBricks

/-! # Boolean composition of the I-brick palette

This module checks the connector network. Geometric restriction and gluing
are separate obligations.
-/

namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def literal (positive value : Bool) : Bool := if positive then value else !value

def topChain (enabled positive outer core : Bool) : Prop :=
  ∃ middle : Bool, (if enabled then middle = !outer else outer = false) ∧
    core = if positive then !middle else middle

def bottomChain (enabled positive core outer : Bool) : Prop :=
  ∃ middle : Bool, middle = (if positive then !core else core) ∧
    (if enabled then outer = !middle else outer = false)

instance (enabled positive outer core : Bool) : Decidable (topChain enabled positive outer core) := by
  unfold topChain
  infer_instance

instance (enabled positive core outer : Bool) : Decidable (bottomChain enabled positive core outer) := by
  unfold bottomChain
  infer_instance

theorem topChain_iff (enabled positive outer core : Bool) :
    topChain enabled positive outer core ↔
      if enabled then core = literal positive outer else outer = false := by
  cases enabled <;> cases positive <;> cases outer <;> cases core <;> decide +kernel

theorem bottomChain_iff (enabled positive core outer : Bool) :
    bottomChain enabled positive core outer ↔
      if enabled then core = literal positive outer else outer = false := by
  cases enabled <;> cases positive <;> cases outer <;> cases core <;> decide +kernel

def CopyRelation (i : Fin 24) (external : Fin 4 → Bool) : Prop :=
  (∀ p, active i p = false → external p = false) ∧
    ∃ value : Bool, ∀ p, active i p = true → external p = value

def ClauseRelation (i : Fin 24) (external : Fin 4 → Bool) : Prop :=
  external 3 = false ∧
    (literal (positive i 0) (external 0) || literal (positive i 1) (external 1) ||
      literal (positive i 2) (external 2)) = true

def Network (i : Fin 24) (external : Fin 4 → Bool) : Prop :=
  ∃ core : Fin 4 → Bool,
    (∀ p, if active i p then core p = literal (positive i p) (external p)
      else external p = false) ∧
    (if i.val < 16 then ∃ value : Bool, ∀ p, core p = value
     else core 3 = false ∧ (core 0 || core 1 || core 2) = true)

instance (i : Fin 24) (external : Fin 4 → Bool) : Decidable (CopyRelation i external) := by
  unfold CopyRelation
  infer_instance

instance (i : Fin 24) (external : Fin 4 → Bool) : Decidable (ClauseRelation i external) := by
  unfold ClauseRelation
  infer_instance

instance (i : Fin 24) (external : Fin 4 → Bool) : Decidable (Network i external) := by
  unfold Network
  infer_instance

/-- The finite connector network implements copying on the selected ports
or the selected signed three-literal clause. -/
theorem network_iff (i : Fin 24) (external : Fin 4 → Bool) :
    Network i external ↔ if i.val < 16 then CopyRelation i external else ClauseRelation i external := by
  revert i external
  decide +kernel

end LeanTrominoes.CompletionPattern.IBricks

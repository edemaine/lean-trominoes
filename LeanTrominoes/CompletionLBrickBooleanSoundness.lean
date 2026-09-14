/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBrickBooleanWitness

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def tableExternal (v : BrickValues) (p : Fin 4) : Bool :=
  if h : p.val < 2 then v ⟨p.val,h⟩ 0 else v ⟨p.val - 2,by omega⟩ 6

def tableCore (v : BrickValues) (p : Fin 4) : Bool :=
  if h : p.val < 2 then v ⟨p.val,h⟩ 2 else v ⟨p.val - 2,by omega⟩ 4

theorem forall_four (P : Fin 4 → Prop) : (∀ p, P p) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3⟩
  · rintro ⟨h0,h1,h2,h3⟩ p
    have cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> assumption

theorem exists_uniform (core : Fin 4 → Bool) :
    (∃ value : Bool, ∀ p, core p = value) ↔ core 0 = core 1 ∧ core 1 = core 2 ∧ core 2 = core 3 := by
  revert core
  decide +kernel

theorem network_witness_expanded (i : Fin 24) (external core : Fin 4 → Bool) :
    NetworkWitness i external core ↔
      ((if active i 0 then core 0 = literal (positive i 0) (external 0) else external 0 = false) ∧
       (if active i 1 then core 1 = literal (positive i 1) (external 1) else external 1 = false) ∧
       (if active i 2 then core 2 = literal (positive i 2) (external 2) else external 2 = false) ∧
       (if active i 3 then core 3 = literal (positive i 3) (external 3) else external 3 = false)) ∧
      (if i.val < 16 then core 0 = core 1 ∧ core 1 = core 2 ∧ core 2 = core 3
       else core 3 = false ∧ (core 0 || core 1 || core 2) = true) := by
  unfold NetworkWitness
  rw [forall_four]
  simp only [exists_uniform]

theorem boolean_ne_chain (a b c : Bool) : a ≠ b → b ≠ c → a = c := by
  revert a b c
  decide +kernel

/-- The major subbrick and its adjacent chains satisfy the brick network
for every locally valid finite table. -/
theorem table_network_witness (i : Fin 24) (v : BrickValues)
    (h : BrickBooleanRelation i v) : NetworkWitness i (tableExternal v) (tableCore v) := by
  rw [network_witness_expanded]
  have chain0 := boolean_ne_chain (v 0 0) (v 0 1) (v 0 2)
  have chain1 := boolean_ne_chain (v 1 0) (v 1 1) (v 1 2)
  have chain2 := boolean_ne_chain (v 0 4) (v 0 5) (v 0 6)
  have chain3 := boolean_ne_chain (v 1 4) (v 1 5) (v 1 6)
  have enumerated : ∀ j : Fin 24, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 := by decide +kernel
  rcases enumerated i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    clear enumerated
    simp [BrickBooleanRelation,layout,upperOuter,lowerOuter,inner,active,positive,bit,
      entryMicroOffset,Atom.BooleanRelation,Cell.add,tableValue,tableExternal,tableCore,literal,
      Bool.eq_not_iff] at h ⊢
    grind

theorem network_of_brick_table (i : Fin 24) (v : BrickValues)
    (h : BrickBooleanRelation i v) : Network i (tableExternal v) :=
  ⟨tableCore v,table_network_witness i v h⟩

end LeanTrominoes.CompletionPattern.LBricks

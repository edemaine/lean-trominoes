/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBooleanPorts
import LeanTrominoes.CompletionIBrickLogic

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

def Atom.BooleanRelation (a : Atom) (value : Cell → Bool) : Prop :=
  match a with
  | .equal => value (0,0) = value (0,1)
  | .negate => value (0,0) ≠ value (0,1)
  | .plugTop => value (0,0) = false
  | .plugBottom => value (0,1) = false
  | .copy => value (0,0) = value (1,0) ∧ value (1,0) = value (0,2) ∧ value (0,2) = value (1,2)
  | .clause => value (1,1) = false ∧ (value (0,0) = true ∨ value (1,0) = false ∨ value (0,1) = true)

instance (a : Atom) (value : Cell → Bool) : Decidable (a.BooleanRelation value) := by
  cases a <;> unfold Atom.BooleanRelation <;> infer_instance

theorem Atom.boolean_completion_iff (a : Atom) (value : Cell → Bool) :
    a.pattern.Completable (a.booleanOutside value) ↔ a.BooleanRelation value := by
  cases a
  · exact equal_boolean_ports value
  · exact negate_boolean_ports value
  · exact plug_top_boolean_ports value
  · exact plug_bottom_boolean_ports value
  · exact copy_boolean_ports value
  · exact clause_boolean_ports value

abbrev BrickValues := Fin 2 → Fin 7 → Bool

def tableValue (v : BrickValues) (c : Cell) : Bool :=
  v ⟨c.1.toNat % 2, Nat.mod_lt _ (by decide)⟩ ⟨c.2.toNat % 7,Nat.mod_lt _ (by decide)⟩

def BrickBooleanRelation (i : Fin 24) (v : BrickValues) : Prop :=
  ∀ entry ∈ layout i, entry.1.BooleanRelation (fun c => tableValue v (Cell.add (entryMicroOffset entry) c))

instance (i : Fin 24) (v : BrickValues) : Decidable (BrickBooleanRelation i v) := by
  unfold BrickBooleanRelation
  infer_instance

def NetworkWitness (i : Fin 24) (external core : Fin 4 → Bool) : Prop :=
  (∀ p, if active i p then core p = literal (positive i p) (external p) else external p = false) ∧
  (if i.val < 16 then ∃ value : Bool, ∀ p, core p = value
   else core 3 = false ∧ (core 0 || core 1 || core 2) = true)

instance (i : Fin 24) (external core : Fin 4 → Bool) : Decidable (NetworkWitness i external core) := by
  unfold NetworkWitness
  infer_instance

def coreSignal (i : Fin 24) (core : Fin 4 → Bool) (p : Fin 4) : Bool :=
  if i.val ≥ 16 ∧ p.val = 1 then !(core p) else core p

def witnessTable (i : Fin 24) (external core : Fin 4 → Bool) (x : Fin 2) (y : Fin 7) : Bool :=
  let top : Fin 4 := ⟨x.val,by omega⟩
  let bottom : Fin 4 := ⟨x.val + 2,by omega⟩
  match y.val with
  | 0 => external top
  | 1 => if positive i top then !(core top) else core top
  | 2 => coreSignal i core top
  | 3 => coreSignal i core top
  | 4 => coreSignal i core bottom
  | 5 => if positive i bottom then !(core bottom) else core bottom
  | _ => external bottom

/-- An explicit assignment to all internal connector rows realizes a
satisfying brick network. This finite certificate checks every palette entry. -/
theorem witness_table_valid (i : Fin 24) (external core : Fin 4 → Bool)
    (h : NetworkWitness i external core) : BrickBooleanRelation i (witnessTable i external core) := by
  revert i external core
  decide +kernel

theorem witness_table_top (i : Fin 24) (external core : Fin 4 → Bool) (x : Fin 2) :
    witnessTable i external core x 0 = external ⟨x.val,by omega⟩ := by rfl

theorem witness_table_bottom (i : Fin 24) (external core : Fin 4 → Bool) (x : Fin 2) :
    witnessTable i external core x 6 = external ⟨x.val + 2,by omega⟩ := by rfl

/-- Every satisfying brick network has a realizable internal Boolean table. -/
theorem brick_table_of_network (i : Fin 24) (external : Fin 4 → Bool) (h : Network i external) :
    ∃ v : BrickValues, BrickBooleanRelation i v ∧
      (∀ x : Fin 2, v x 0 = external ⟨x.val,by omega⟩) ∧
      (∀ x : Fin 2, v x 6 = external ⟨x.val + 2,by omega⟩) := by
  obtain ⟨core,h⟩ := h
  exact ⟨witnessTable i external core,witness_table_valid i external core h,
    witness_table_top i external core,witness_table_bottom i external core⟩

end LeanTrominoes.CompletionPattern.IBricks

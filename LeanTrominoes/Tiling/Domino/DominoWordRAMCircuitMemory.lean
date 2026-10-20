/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitStep

/-! # Memory refinement for consecutive binary circuit nodes -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

theorem slotBase_mono (base length : ℕ) {a b : ℕ} (h : a≤b) :
    slotBase base length a≤slotBase base length b := Nat.add_le_add_left (Nat.mul_le_mul_right length h) base

@[simp] theorem slotBase_succ (base length slot : ℕ) :
    slotBase base length (slot+1)=slotBase base length slot+length := by
  simp [slotBase,Nat.add_mul,Nat.add_assoc]

theorem digit_before {base length earlier later digit : ℕ} (order : earlier< later) (within : digit< length) :
    slotBase base length earlier+digit<slotBase base length later := by
  have grow := slotBase_mono base length (show earlier+1≤later by omega)
  rw [slotBase_succ] at grow
  omega

theorem digit_after {base length earlier later digit : ℕ} (order : earlier< later) :
    slotBase base length earlier+length≤slotBase base length later+digit := by
  have grow := slotBase_mono base length (show earlier+1≤later by omega)
  rw [slotBase_succ] at grow
  omega

structure Represents (base length count : ℕ) (values : ℕ → ZMod (2^length)) (data : Data) : Prop where
  base_eq : data.1 baseRegister=base
  length_eq : data.1 (low Reg.length)=length
  bits : ∀ slot< count, ∀ i< length, data.2 (slotBase base length slot+i)≤1
  value : ∀ slot< count, (Binary.value data.2 (slotBase base length slot) length : ZMod (2^length))=values slot

/-- A fresh node adds one represented value while preserving all its inputs. -/
theorem Represents.advance {base length count : ℕ} {values : ℕ → ZMod (2^length)}
    {before after : Data} {node : Node} (h : Represents base length count values before)
    (valid : node.Valid count) (step : StepResult node base length count before.2 after) :
    Represents base length (count+1) (node.advance count values) after := by
  constructor
  · exact step.base_eq
  · exact step.length_eq
  · intro slot hs i hi
    by_cases current : slot=count
    · subst slot
      exact step.bits i hi
    · have earlier : slot< count := by omega
      rw [step.frame _ (Or.inl (digit_before earlier hi))]
      exact h.bits slot earlier i hi
  · intro slot hs
    by_cases current : slot=count
    · subst slot
      simp only [Node.advance,Function.update_self]
      exact step.value.trans (Node.eval_congr valid h.value)
    · have earlier : slot< count := by omega
      have unchanged : Binary.value after.2 (slotBase base length slot) length=
          Binary.value before.2 (slotBase base length slot) length :=
        value_congr (fun i hi => step.frame _ (Or.inl (digit_before earlier hi)))
      rw [unchanged,h.value slot earlier]
      exact (Function.update_of_ne current _ _).symm

/-- Later, still-unused array slots remain zero after one node. -/
theorem StepResult.future_zero {base length count limit : ℕ} {node : Node} {source : ℕ → ℕ} {after : Data}
    (h : StepResult node base length count source after)
    (zero : ∀ slot, count≤slot → slot< limit → ∀ i< length, source (slotBase base length slot+i)=0) :
    ∀ slot, count+1≤slot → slot< limit → ∀ i< length, after.2 (slotBase base length slot+i)=0 := by
  intro slot later within i hi
  rw [h.frame _ (Or.inr (digit_after (by omega : count< slot)))]
  exact zero slot (by omega) within i hi

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

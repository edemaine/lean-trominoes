/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import Mathlib.Tactic

/-! # Composing bounded-word RAM instruction executions

`RunsTo` counts primitive instructions that continue execution. It composes
prefixes without treating a Lean function or a solver call as a RAM instruction.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM

inductive RunsTo {r : ℕ} (w : ℕ) (program : List (Instruction r)) : State r → State r → ℕ → Prop
  | refl (s) : RunsTo w program s s 0
  | next {s u t n} : step w program s = .next u →
      RunsTo w program u t n → RunsTo w program s t (n+1)

namespace RunsTo

theorem single {r w : ℕ} {program : List (Instruction r)} {s t : State r}
    (transition : step w program s = .next t) : RunsTo w program s t 1 :=
  .next transition (.refl t)

theorem trans {r w : ℕ} {program : List (Instruction r)} {s u t : State r} {n m : ℕ}
    (first : RunsTo w program s u n) (second : RunsTo w program u t m) :
    RunsTo w program s t (n+m) := by
  induction first with
  | refl => simpa using second
  | next transition _ ih =>
    have joined := RunsTo.next transition (ih second)
    simpa only [Nat.add_right_comm,Nat.add_assoc] using joined

theorem executes {r w : ℕ} {program : List (Instruction r)} {s t : State r} {n m : ℕ} {value : ℤ}
    (trace : RunsTo w program s t n) (suffix : Executes w program t value m) :
    Executes w program s value (n+m) := by
  induction trace with
  | refl => simpa using suffix
  | next transition _ ih =>
    have joined := Executes.next transition (ih suffix)
    simpa only [Nat.add_right_comm,Nat.add_assoc] using joined

end RunsTo

/-- Registers and memory, without the control location. -/
abbrev Data (r : ℕ) := (Fin r → ℤ) × (ℕ → ℤ)

def Data.at {r : ℕ} (data : Data r) (pc : ℕ) : State r := ⟨pc,data.1,data.2⟩

def State.data {r : ℕ} (s : State r) : Data r := (s.registers,s.memory)

/-- A bytecode fragment occupies the given consecutive instruction addresses. -/
def Contains {r : ℕ} (program : List (Instruction r)) (base : ℕ) (fragment : List (Instruction r)) : Prop :=
  ∀ i, i<fragment.length → program[base+i]?=fragment[i]?

namespace Contains

theorem self {r : ℕ} (program : List (Instruction r)) : Contains program 0 program := by
  intro i _
  simp

theorem append_left {r : ℕ} {program a b : List (Instruction r)} {base : ℕ}
    (h : Contains program base (a++b)) : Contains program base a := by
  intro i hi
  rw [h i (by simp; omega)]
  exact List.getElem?_append_left hi

theorem append_right {r : ℕ} {program a b : List (Instruction r)} {base : ℕ}
    (h : Contains program base (a++b)) : Contains program (base+a.length) b := by
  intro i hi
  have hit := h (a.length+i) (by simp; omega)
  simpa [Nat.add_assoc,List.getElem?_append_right (Nat.le_add_right _ _)] using hit

theorem singleton {r : ℕ} {program : List (Instruction r)} {base : ℕ} {op : Instruction r}
    (h : Contains program base [op]) : program[base]?=some op := by
  simpa using h 0 (by simp)

theorem append {r : ℕ} (a b : List (Instruction r)) : Contains (a++b) 0 a :=
  (Contains.self (a++b)).append_left

end Contains

/-- The effect of an instruction depends only on the instruction fetched at the PC. -/
theorem step_congr {r w : ℕ} {a b : List (Instruction r)} {s : State r}
    (fetch : a[s.pc]?=b[s.pc]?) : step w a s=step w b s := by
  simp only [step,fetch]

/-- A branch or jump that lands within the address space is one real instruction. -/
theorem run_jump {r w : ℕ} {program : List (Instruction r)} {data : Data r} {pc target : ℕ}
    (fetch : program[pc]?=some (.jump target)) (source : pc<2^w) (destination : target<2^w) :
    RunsTo w program (data.at pc) (data.at target) 1 := by
  apply RunsTo.single
  simp [step,Data.at,fetch,not_le.mpr source,next,destination]

end LeanTrominoes.ComplexityAbstract.RAM

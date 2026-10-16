/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract

/-! # Checks of the formal abstract's RAM semantics -/

namespace LeanTrominoes.ComplexityAbstract.RAM

/-- Successful executions cannot have zero cost. -/
theorem executes_positive {r : ℕ} {program : List (Instruction r)} {s : State r}
    {value : ℤ} {n : ℕ} (execution : Executes program s value n) : 0 < n := by
  cases execution <;> omega

/-- Faults cannot masquerade as successful outputs. -/
theorem fault_not_executes {r : ℕ} {program : List (Instruction r)} {s : State r}
    (fault : step program s = .fault) (value : ℤ) (n : ℕ) :
    ¬ Executes program s value n := by
  intro execution
  cases execution with
  | halt h => rw [fault] at h; cases h
  | next h _ => rw [fault] at h; cases h

/-- A fixed program and input determine both the output and the exact cost. -/
theorem executes_deterministic {r : ℕ} {program : List (Instruction r)} {s : State r}
    {v w : ℤ} {n m : ℕ} (first : Executes program s v n)
    (second : Executes program s w m) : v = w ∧ n = m := by
  induction first generalizing w m with
  | halt hs =>
    cases second with
    | halt ht => exact ⟨Outcome.halt.inj (hs.symm.trans ht), rfl⟩
    | next ht _ => rw [hs] at ht; cases ht
  | next hs tail ih =>
    cases second with
    | halt ht => rw [hs] at ht; cases ht
    | next ht rest =>
      have same := Outcome.next.inj (hs.symm.trans ht)
      cases same
      obtain ⟨value, steps⟩ := ih rest
      exact ⟨value, congrArg Nat.succ steps⟩

/-- A real finite program reads its first input word through an indirect
address and branches on its sign. Both paths use exactly six instructions. -/
def signProgram : List (Instruction 2) :=
  [.constant 0 1, .load 1 0, .constant 0 0, .branchLt 1 0 6,
    .constant 0 0, .halt 0, .constant 0 1, .halt 0]

theorem signProgram_executes (x : ℤ) :
    Executes signProgram (initial [x]) (if x < 0 then 1 else 0) 6 := by
  by_cases h : x < 0
  · simp only [h, ite_true]
    apply Executes.next (by rfl)
    apply Executes.next (by rfl)
    apply Executes.next (by rfl)
    apply Executes.next (by simp [step, signProgram, initial, writeRegister, h]; rfl)
    apply Executes.next (by rfl)
    exact Executes.halt rfl
  · simp only [h, ite_false]
    apply Executes.next (by rfl)
    apply Executes.next (by rfl)
    apply Executes.next (by rfl)
    apply Executes.next (by simp [step, signProgram, initial, writeRegister, h]; rfl)
    apply Executes.next (by rfl)
    exact Executes.halt rfl

theorem sign_decides : DecidesWithin (fun x : ℤ => [x]) (fun x => x < 0) (fun _ => 6) := by
  refine ⟨2, signProgram, fun x => ⟨6, (if x < 0 then 1 else 0), signProgram_executes x,
    le_rfl, ?_, ?_⟩⟩
  · split <;> simp
  · split <;> simp_all

end LeanTrominoes.ComplexityAbstract.RAM

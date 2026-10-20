/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract

/-! # Proofs and regression checks for the bounded-word RAM

This verification module is outside the public abstract suite. The machine and
all complexity definitions, including `LeanTrominoes.ComplexityAbstract.RAM.DecidesWithin`,
are explicitly defined in `ComplexityAbstract.lean`. The sign test below is a
model regression, not one of the graph or tiling abstract's main results.
-/

namespace LeanTrominoes.ComplexityAbstract.RAM

/-- Successful executions cannot have zero cost. -/
theorem executes_positive {r w : ℕ} {program : List (Instruction r)} {s : State r}
    {value : ℤ} {n : ℕ} (execution : Executes w program s value n) : 0 < n := by
  cases execution <;> omega

/-- Faults cannot masquerade as successful outputs. -/
theorem fault_not_executes {r w : ℕ} {program : List (Instruction r)} {s : State r}
    (fault : step w program s = .fault) (value : ℤ) (n : ℕ) :
    ¬ Executes w program s value n := by
  intro execution
  cases execution with
  | halt h => rw [fault] at h; cases h
  | next h _ => rw [fault] at h; cases h

/-- A fixed program and input determine both the output and the exact cost. -/
theorem executes_deterministic {r w : ℕ} {program : List (Instruction r)} {s : State r}
    {v output : ℤ} {n m : ℕ} (first : Executes w program s v n)
    (second : Executes w program s output m) : v = output ∧ n = m := by
  induction first generalizing output m with
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

/-- The mathematical store represents only word-sized data, including unused cells. -/
def State.Bounded {r : ℕ} (w : ℕ) (s : State r) : Prop :=
  s.pc < 2^w ∧ (∀ i, Fits w (s.registers i)) ∧ ∀ a, Fits w (s.memory a)

private theorem next_bounded {r w : ℕ} {s t : State r}
    (data : (∀ i, Fits w (s.registers i)) ∧ ∀ a, Fits w (s.memory a))
    (transition : next w s = .next t) : t.Bounded w := by
  unfold next at transition
  split at transition
  · cases transition
    exact ⟨by assumption,data⟩
  · cases transition

private theorem write_bounded {r w : ℕ} {s t : State r} {dst : Fin r} {value : ℤ}
    (bounded : s.Bounded w) (transition : write w s dst value = .next t) : t.Bounded w := by
  unfold write at transition
  split at transition
  · apply next_bounded (s := writeRegister s dst value) ?_ transition
    refine ⟨fun i => ?_,bounded.2.2⟩
    simp only [writeRegister]
    by_cases equal : i=dst
    · subst i
      simpa using (show Fits w value by assumption)
    · simpa [Function.update_of_ne equal] using bounded.2.1 i
  · cases transition

/-- No successful instruction creates a value outside the signed word range
or a program counter outside the unsigned address range. -/
theorem step_preserves_bounded {r w : ℕ} {program : List (Instruction r)} {s t : State r}
    (bounded : s.Bounded w) (transition : step w program s = .next t) : t.Bounded w := by
  unfold step at transition
  split at transition
  · cases transition
  · cases instruction : program[s.pc]? with
    | none => simp [instruction] at transition
    | some op =>
      rw [instruction] at transition
      cases op <;> dsimp only at transition
      case constant dst value => exact write_bounded bounded transition
      case copy dst src => exact write_bounded bounded transition
      case arithmetic op dst left right => exact write_bounded bounded transition
      case load dst address =>
        split at transition
        · cases transition
        · exact write_bounded bounded transition
      case store address src =>
        split at transition
        · cases transition
        · apply next_bounded (s := { pc := s.pc+1, registers := s.registers, memory := Function.update s.memory (s.registers address).toNat (s.registers src) }) ?_ transition
          refine ⟨bounded.2.1,fun a => ?_⟩
          by_cases equal : a=(s.registers address).toNat
          · subst a
            simpa using bounded.2.1 src
          · simpa [Function.update_of_ne equal] using bounded.2.2 a
      case jump target => exact next_bounded (s := { s with pc := target }) bounded.2 transition
      case branchEq left right target => exact next_bounded (s := { s with pc := if s.registers left=s.registers right then target else s.pc+1 }) bounded.2 transition
      case branchLt left right target => exact next_bounded (s := { s with pc := if s.registers left<s.registers right then target else s.pc+1 }) bounded.2 transition
      case halt result => split at transition <;> cases transition

/-- A real finite program reads its first input word through an indirect
address and branches on its sign. Both paths use exactly six instructions. -/
def signProgram : List (Instruction 2) :=
  [.constant 0 1, .load 1 0, .constant 0 0, .branchLt 1 0 6,
    .constant 0 0, .halt 0, .constant 0 1, .halt 0]

theorem fits_zero {w : ℕ} (positive : 0<w) : Fits w 0 := by
  have power : (0:ℤ) < 2^(w-1) := pow_pos (by decide) _
  exact ⟨positive,by omega,power⟩

theorem fits_one {w : ℕ} (wide : 2≤w) : Fits w 1 := by
  have power : (2:ℤ) ≤ 2^(w-1) := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 1≤w-1 by omega))
  exact ⟨by omega,by omega,by omega⟩

/-- A fitting input starts with word-sized registers and memory at every address. -/
theorem initial_bounded {r w : ℕ} {input : List ℤ} (fits : InputFits w input) :
    (initial (r := r) input).Bounded w := by
  have zero := fits_zero fits.1.1
  refine ⟨by simp [initial],fun _ => zero,fun a => ?_⟩
  simp only [initial]
  split
  · exact fits.1
  · cases lookup : input[a-1]? with
    | none => simpa [lookup] using zero
    | some value =>
      simpa [lookup] using fits.2 value (List.mem_of_getElem? lookup)

/-- Every finite execution prefix from a fitting input stays within the word range. -/
theorem reachable_bounded {r w : ℕ} {program : List (Instruction r)} {input : List ℤ}
    (fits : InputFits w input) {s : State r}
    (reachable : Relation.ReflTransGen (fun before after => step w program before = .next after)
      (initial input) s) : s.Bounded w := by
  induction reachable with
  | refl => exact initial_bounded fits
  | tail _ transition ih => exact step_preserves_bounded ih transition

theorem signProgram_executes (w : ℕ) (wide : 4≤w) (x : ℤ) (fits : Fits w x) :
    Executes w signProgram (initial [x]) (if x < 0 then 1 else 0) 6 := by
  have capacity : 8 ≤ 2^w := by
    have := Nat.pow_le_pow_right (by decide : 1≤2) wide
    norm_num at this ⊢
    omega
  have pc0 : 0 < 2^w := by omega
  have pc1 : 1 < 2^w := by omega
  have pc2 : 2 < 2^w := by omega
  have pc3 : 3 < 2^w := by omega
  have pc4 : 4 < 2^w := by omega
  have pc5 : 5 < 2^w := by omega
  have pc6 : 6 < 2^w := by omega
  have pc7 : 7 < 2^w := by omega
  have address1 : (1:ℤ) < (2^w:ℕ) := by exact_mod_cast pc1
  have zero := fits_zero (show 0<w by omega)
  have one := fits_one (show 2≤w by omega)
  let s1 := writeRegister (initial (r := 2) [x]) 0 1
  let s2 := writeRegister s1 1 x
  let s3 := writeRegister s2 0 0
  apply Executes.next (t := s1)
    (by simp_all [s1,step,signProgram,List.getElem?_cons,initial,write,next,writeRegister])
  apply Executes.next (t := s2)
    (by simp_all [s1,s2,step,signProgram,List.getElem?_cons,initial,write,next,writeRegister])
  apply Executes.next (t := s3)
    (by simp_all [s1,s2,s3,step,signProgram,List.getElem?_cons,initial,write,next,writeRegister])
  by_cases h : x < 0
  · simp only [h, ite_true]
    let s4 : State 2 := { s3 with pc := 6 }
    let s5 := writeRegister s4 0 1
    apply Executes.next (t := s4)
      (by simp [s1,s2,s3,s4,step,signProgram,List.getElem?_cons,initial,next,writeRegister,not_le.mpr pc3,pc6,h])
    apply Executes.next (t := s5)
      (by simp_all [s1,s2,s3,s4,s5,step,signProgram,List.getElem?_cons,initial,write,next,writeRegister])
    exact Executes.halt
      (by simp_all [s1,s2,s3,s4,s5,step,signProgram,List.getElem?_cons,initial,writeRegister])
  · simp only [h, ite_false]
    let s4 : State 2 := { s3 with pc := 4 }
    let s5 := writeRegister s4 0 0
    apply Executes.next (t := s4)
      (by simp [s1,s2,s3,s4,step,signProgram,List.getElem?_cons,initial,next,writeRegister,not_le.mpr pc3,pc4,h])
    apply Executes.next (t := s5)
      (by simp_all [s1,s2,s3,s4,s5,step,signProgram,List.getElem?_cons,initial,write,next,writeRegister])
    exact Executes.halt
      (by simp_all [s1,s2,s3,s4,s5,step,signProgram,List.getElem?_cons,initial,writeRegister])

theorem sign_decides : LeanTrominoes.ComplexityAbstract.RAM.DecidesWithin (fun x : ℤ => [x]) (fun x => x < 0)
    (fun _ => 6) (fun _ => 4) := by
  refine ⟨2,signProgram,fun x w wide input => ⟨6,(if x<0 then 1 else 0),?_,le_rfl,?_,?_⟩⟩
  · exact signProgram_executes w wide x (input.2 x (by simp))
  · split <;> simp
  · split <;> simp_all

/-- Adding two representable values can overflow, and then the machine faults. -/
theorem overflowing_add_faults :
    step 4 [.arithmetic .add 0 0 0] ({ pc := 0,registers := fun _ : Fin 1 => 7,memory := fun _ => 0 }) =
      .fault := by rfl

/-- A program cannot branch beyond the unsigned word address space. -/
theorem oversized_jump_faults : step 4 [.jump 16] (initial (r := 1) []) = .fault := by rfl

end LeanTrominoes.ComplexityAbstract.RAM

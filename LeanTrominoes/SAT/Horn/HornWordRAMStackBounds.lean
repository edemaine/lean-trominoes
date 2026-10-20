/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStack

/-! # Word and instruction bounds for initializing the Horn stack -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.rules Reg.heads Reg.counters Reg.stack
  Reg.index Reg.rule Reg.value Reg.top Reg.scratch Reg.headValue

/-- The scan increments its index once and pushes at most one head. -/
theorem stackBody_control (data : Data) :
    (stackBodyState data).1 Reg.index=data.1 Reg.index+data.1 Reg.one ∧
    (stackBodyState data).1 Reg.one=data.1 Reg.one ∧
    (stackBodyState data).1 Reg.zero=data.1 Reg.zero ∧
    (stackBodyState data).1 Reg.rules=data.1 Reg.rules ∧
    (stackBodyState data).1 Reg.top≤data.1 Reg.top+data.1 Reg.one := by
  unfold stackBodyState stackBranch
  split <;> simp [pushState_registers,stackRead,readState,NaturalData.set]

/-- Unlike a repeated coarse doubling bound, this bound grows additively
through the scan. Only original head values are stored in memory. -/
theorem stackBody_bounds {R M : ℕ} (data : Data)
    (regs : ∀ i, data.1 i≤R) (memory : ∀ a, data.2 a≤M) (unit : data.1 Reg.one=1) :
    (∀ i, (stackBodyState data).1 i≤R+M+data.1 Reg.index+data.1 Reg.top+2) ∧
    (∀ a, (stackBodyState data).2 a≤M) := by
  let bound := R+M+data.1 Reg.index+data.1 Reg.top+2
  have loaded : ∀ i, (stackRead data).1 i≤bound := by
    simp only [stackRead,readState,NaturalData.set]
    apply update_bound
    · apply update_bound
      · intro i; exact (regs i).trans (by dsimp [bound]; omega)
      · have h : data.1 14≤R := regs Reg.counters; dsimp [bound]; omega
    · exact (memory _).trans (by dsimp [bound]; omega)
  have loadedMem : (stackRead data).2=data.2 := rfl
  have branch : (∀ i, (stackBranch data).1 i≤bound) ∧ (∀ a, (stackBranch data).2 a≤M) := by
    unfold stackBranch
    split
    · constructor
      · rw [pushState_registers]
        apply update_bound
        · apply update_bound
          · apply update_bound
            · exact update_bound loaded Reg.rule ((regs Reg.index).trans (by dsimp [bound]; omega))
            · simp only [NaturalData.set,loadedMem]
              exact (memory _).trans (by dsimp [bound]; omega)
          · simpa [stackRead,readState,NaturalData.set] using
              (show data.1 Reg.stack+data.1 Reg.top≤bound by have h : data.1 16≤R := regs Reg.stack; dsimp [bound]; omega)
        · simpa [stackRead,readState,NaturalData.set,unit] using
            (show data.1 Reg.top+1≤bound by have := regs Reg.top; dsimp [bound]; omega)
      · rw [pushState_memory]
        exact update_bound memory _ (memory _)
    · exact ⟨loaded,memory⟩
  constructor
  · simp only [stackBodyState,NaturalData.set]
    apply update_bound branch.1
    have controls := stackBody_control data
    have value : (stackBranch data).1 Reg.index+(stackBranch data).1 Reg.one=
        data.1 Reg.index+1 := by
      have eq := controls.1
      simpa only [stackBodyState,NaturalData.set,Function.update_self,unit] using eq
    rw [value]
    have := regs Reg.index
    dsimp [bound]
    omega
  · exact branch.2

theorem stackBodyCost_le (data : Data) : stackBodyCost data≤10 := by
  unfold stackBodyCost
  split <;> omega

/-- The exact cost sum includes each loop branch and back jump. -/
def stackLoopCost (data : Data) : ℕ → ℕ
  | 0 => 2
  | n+1 => stackBodyCost data+stackLoopCost (stackBodyState data) n+2

theorem stackLoopCost_le (data : Data) (n : ℕ) : stackLoopCost data n≤12*n+2 := by
  induction n generalizing data with
  | zero => simp [stackLoopCost]
  | succ n ih =>
    have rest := ih (stackBodyState data)
    have body := stackBodyCost_le data
    simp only [stackLoopCost]
    omega

theorem stackLoop_exec {w bound remaining : ℕ} (data : Data)
    (unit : data.1 Reg.one=1) (length : data.1 Reg.index+remaining=data.1 Reg.rules)
    (bounded : ∀ k, k<remaining → NaturalData.Bounded bound ((stackBodyState^[k]) data))
    (width : Fits w (64*bound : ℕ)) :
    NaturalData.Exec w (.loop (.lt Reg.index Reg.rules) initialStackBody) data
      ((stackBodyState^[remaining]) data) (stackLoopCost data remaining) := by
  induction remaining generalizing data with
  | zero =>
    apply Structured.Exec.loop_done
    simp only [Structured.Condition.Holds,NaturalData.word]
    exact_mod_cast (show ¬data.1 Reg.index<data.1 Reg.rules by omega)
  | succ n ih =>
    have body := stackBody_exec (bounded 0 (by omega)) width
    have control := stackBody_control data
    have tail := ih (stackBodyState data) (control.2.1.trans unit)
      (by rw [control.1,control.2.2.2.1,unit]; omega)
      (fun k hk => by simpa only [Function.iterate_succ_apply] using bounded (k+1) (by omega))
    have run := Structured.Exec.loop_more
      (show Structured.Condition.Holds (.lt Reg.index Reg.rules) data.word by
        simp only [Structured.Condition.Holds,NaturalData.word]
        exact_mod_cast (show data.1 Reg.index<data.1 Reg.rules by omega)) body tail
    simpa only [stackLoopCost,Function.iterate_succ_apply,Function.iterate_zero,id_eq] using run

/-- Every scan prefix has a polynomial word bound, including scratch addresses. -/
theorem stack_prefix_bounds {B : ℕ} (data : Data) (initial : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (index : data.1 Reg.index=0) (top : data.1 Reg.top=0)
    (k : ℕ) :
    (∀ i, ((stackBodyState^[k]) data).1 i≤B+k*(B+2*k+2)) ∧
    (∀ a, ((stackBodyState^[k]) data).2 a≤B) ∧
    ((stackBodyState^[k]) data).1 Reg.index=k ∧
    ((stackBodyState^[k]) data).1 Reg.top≤k ∧
    ((stackBodyState^[k]) data).1 Reg.one=1 := by
  induction k with
  | zero => simpa [index,top] using And.intro initial.1 (And.intro initial.2 (And.intro index (And.intro top.le unit)))
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have bound := stackBody_bounds ((stackBodyState^[k]) data) ih.1 ih.2.1 ih.2.2.2.2
    have controls := stackBody_control ((stackBodyState^[k]) data)
    refine ⟨?_,bound.2,by omega,by omega,by omega⟩
    intro i
    have := bound.1 i
    nlinarith [ih.2.2.1,ih.2.2.2.1]

def stackBound (B rules : ℕ) : ℕ := B+rules*(B+2*rules+2)

theorem stack_prefix_bounded {B : ℕ} (data : Data) (initial : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (index : data.1 Reg.index=0) (top : data.1 Reg.top=0)
    (rules k : ℕ) (within : k≤rules) :
    NaturalData.Bounded (stackBound B rules) ((stackBodyState^[k]) data) := by
  have bounds := stack_prefix_bounds data initial unit index top k
  constructor
  · intro i
    have value := bounds.1 i
    have product := Nat.mul_le_mul within (show B+2*k+2≤B+2*rules+2 by omega)
    dsimp [stackBound]
    omega
  · intro address
    exact (bounds.2.1 address).trans (by dsimp [stackBound]; omega)

def stackStart (data : Data) : Data := (data.set Reg.top 0).set Reg.index 0

def stackedState (data : Data) : Data := (stackBodyState^[data.1 Reg.rules]) (stackStart data)

def initialStackCost (data : Data) : ℕ := 2+stackLoopCost (stackStart data) (data.1 Reg.rules)

theorem initialStackCost_le (data : Data) : initialStackCost data≤12*data.1 Reg.rules+4 := by
  have bound := stackLoopCost_le (stackStart data) (data.1 Reg.rules)
  change 2+stackLoopCost (stackStart data) (data.1 Reg.rules)≤12*data.1 Reg.rules+4
  omega

/-- The entire scan executes, including both register initializations and the
final failed loop test. The word size covers a polynomial in the initial data. -/
theorem initialStack_exec {w B : ℕ} {data : Data} (initial : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (width : Fits w (64*stackBound B (data.1 Reg.rules) : ℕ)) :
    NaturalData.Exec w initialStack data (stackedState data) (initialStackCost data) := by
  have zero : Fits w (0 : ℕ) := Allocation.nat_fits_le width (Nat.zero_le _)
  have a := NaturalData.constant_exec data Reg.top 0 zero
  have b := NaturalData.constant_exec (data.set Reg.top 0) Reg.index 0 zero
  have startBound : NaturalData.Bounded B (stackStart data) :=
    (initial.set Reg.top (Nat.zero_le B)).set Reg.index (Nat.zero_le B)
  have startOne : (stackStart data).1 Reg.one=1 := by simpa [stackStart,NaturalData.set] using unit
  have run := stackLoop_exec (stackStart data) startOne
    (by simp [stackStart,NaturalData.set])
    (fun k hk => stack_prefix_bounded (stackStart data) startBound startOne
      (by simp [stackStart,NaturalData.set]) (by simp [stackStart,NaturalData.set])
      (data.1 Reg.rules) k hk.le) width
  simpa only [initialStack,constant,stackedState,initialStackCost,← Nat.add_assoc,Nat.reduceAdd,
    stackStart,NaturalData.set,Function.update_of_ne (show Reg.rules≠Reg.index by decide),
    Function.update_of_ne (show Reg.rules≠Reg.top by decide)] using a.seq (b.seq run)

end LeanTrominoes.Horn.WordRAM

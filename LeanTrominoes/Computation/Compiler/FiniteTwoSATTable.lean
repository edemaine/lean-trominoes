/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATExpressions
import LeanTrominoes.Computation.RAM.Allocation
import Mathlib.Data.Fin.SuccPred

/-! # A verified flat table-generation loop

An expression computes each output cell from the loop index and memory. The
loop executes its actual primitive arithmetic/load code, stores the result,
and increments the index. Its count includes every branch and loop-back jump.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

def prefixMemory (original : ℕ → ℤ) (base : ℕ) (values : ℕ → ℤ) (count : ℕ) : ℕ → ℤ :=
  fun address => if base≤address ∧ address<base+count then values (address-base) else original address

theorem prefixMemory_zero (original : ℕ → ℤ) (base : ℕ) (values : ℕ → ℤ) :
    prefixMemory original base values 0=original := by funext a; simp [prefixMemory]

theorem prefixMemory_succ (original : ℕ → ℤ) (base : ℕ) (values : ℕ → ℤ) (count : ℕ) :
    prefixMemory original base values (count+1)=
      Function.update (prefixMemory original base values count) (base+count) (values count) := by
  funext address
  by_cases equal : address=base+count
  · subst address; simp [prefixMemory]
  · simp only [Function.update_of_ne equal,prefixMemory]
    split_ifs <;> first | rfl | omega

namespace Table
variable {k : ℕ} (e : Expr (k+5))

def reg (i : Fin (k+5)) : Fin e.registers := e.inputRegister i
abbrev address : Fin e.registers := reg e 0
abbrev index : Fin e.registers := reg e 1
abbrev length : Fin e.registers := reg e 2
abbrev base : Fin e.registers := reg e 3
abbrev one : Fin e.registers := reg e 4

attribute [local simp] reg Expr.inputRegister address index length base one

def body : Structured.Code e.registers :=
  .seq e.program (.seq (.atom (.arithmetic .add (address e) (base e) (index e)))
    (.seq (.atom (.store (address e) (e.temporary 0)))
      (.atom (.arithmetic .add (index e) (index e) (one e)))))

def program : Structured.Code e.registers := .loop (.lt (index e) (length e)) (body e)

def Controls (data : Data e.registers) (start stop output : ℕ) : Prop :=
  data.1 (index e)=start ∧ data.1 (length e)=stop ∧ data.1 (base e)=output ∧ data.1 (one e)=1

theorem temporary_ne_reg (i : Fin (k+5)) : e.temporary 0≠reg e i := by
  intro equal
  have h := congrArg Fin.val equal
  rw [e.temporary_val 0 e.nodes_positive] at h
  simp at h
  omega

theorem body_exec {w start stop output : ℕ} (data : Data e.registers)
    (controls : Controls e data start stop output) (safe : e.Safe w (fun i => data.1 (reg e i)) data.2)
    (addressFits : Fits w (output+start : ℕ)) (nextFits : Fits w (start+1 : ℕ))
    (valueFits : Fits w (e.eval (fun i => data.1 (reg e i)) data.2)) :
    ∃ result, Structured.Exec w (body e) data result (e.nodes+3) ∧
      Controls e result (start+1) stop output ∧
      result.2=Function.update data.2 (output+start) (e.eval (fun i => data.1 (reg e i)) data.2) ∧
      ∀ i : Fin (k+5), 5≤ i.val → result.1 (reg e i)=data.1 (reg e i) := by
  have mod2 : 2%(k+5)=2 := Nat.mod_eq_of_lt (by omega)
  have mod3 : 3%(k+5)=3 := Nat.mod_eq_of_lt (by omega)
  have mod4 : 4%(k+5)=4 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨middle,expression,memory,value,preserved⟩ := e.program_exec (fun i => data.1 (reg e i)) data
    (fun _ => rfl) safe
  have mid : Controls e middle start stop output := by
    simpa only [Controls,reg,preserved] using controls
  let addressed := set middle (address e) (output+start : ℕ)
  have addressExec : Structured.Exec w (.atom (.arithmetic .add (address e) (base e) (index e)))
      middle addressed 1 := by
    apply Structured.Exec.atom
    simp only [Structured.Primitive.eval,mid.1,mid.2.2.1,Arithmetic.eval,← Nat.cast_add,addressFits,
      ite_true,addressed,set]
  let stored : Data e.registers := (addressed.1,Function.update data.2 (output+start)
    (e.eval (fun i => data.1 (reg e i)) data.2))
  have storeExec : Structured.Exec w (.atom (.store (address e) (e.temporary 0))) addressed stored 1 := by
    apply Structured.Exec.atom
    have kept : addressed.1 (e.temporary 0)=e.eval (fun i => data.1 (reg e i)) data.2 := by
      simpa only [addressed,set,Function.update_of_ne (temporary_ne_reg e 0)] using value
    have valid : ¬((output+start : ℕ) : ℤ)<0 := Int.not_lt.mpr (Int.natCast_nonneg _)
    have fitsAddress : ((output+start : ℕ) : ℤ)<(2^w : ℕ) := by
      exact Allocation.nat_address addressFits
    have addrValue : addressed.1 (address e)=(output+start : ℕ) := by simp [addressed,set]
    have addrMemory : addressed.2=data.2 := memory
    simp only [Structured.Primitive.eval,addrValue,kept,valid,not_le.mpr fitsAddress,
      valueFits,not_true_eq_false,or_self,ite_false,Int.toNat_natCast,stored,addrMemory]
  let result := set stored (index e) (start+1 : ℕ)
  have incrementExec : Structured.Exec w (.atom (.arithmetic .add (index e) (index e) (one e))) stored result 1 := by
    apply Structured.Exec.atom
    have idx : stored.1 (index e)=start := by simpa [stored,addressed,set,Function.update_apply,Fin.castAdd_inj,Fin.ext_iff,mod2,mod3,mod4] using mid.1
    have unit : stored.1 (one e)=1 := by simpa [stored,addressed,set,Function.update_apply,Fin.castAdd_inj,Fin.ext_iff,mod2,mod3,mod4] using mid.2.2.2
    have fits' := nextFits
    simp only [Nat.cast_add,Nat.cast_one] at fits'
    simp only [Structured.Primitive.eval,idx,unit,Arithmetic.eval,fits',ite_true,result,set,Nat.cast_add,Nat.cast_one]
  refine ⟨result,?_,?_,rfl,?_⟩
  · simpa only [body,Nat.add_assoc] using expression.seq (addressExec.seq (storeExec.seq incrementExec))
  · simpa [Controls,result,stored,addressed,set,Function.update_apply,Fin.castAdd_inj,Fin.ext_iff,mod2,mod3,mod4] using And.intro mid.2.1 (And.intro mid.2.2.1 mid.2.2.2)

  · intro i hi
    have zero : i≠0 := by intro eq; rw [eq] at hi; simp at hi
    have one : i≠1 := by intro eq; rw [eq] at hi; simp at hi
    have notAddress : reg e i≠address e := by
      intro equal
      have h := congrArg Fin.val equal
      exact zero (Fin.ext h)
    have notIndex : reg e i≠index e := by
      intro equal
      have h := congrArg Fin.val equal
      exact one (Fin.ext h)
    dsimp only [result,set,stored,addressed]
    rw [Function.update_of_ne notIndex,Function.update_of_ne notAddress]
    exact preserved i

/-- A pointwise arithmetic/load expression generates an entire table. The
hypothesis verifies its actual loads and intermediate values at each index;
it is never treated as a unit-cost operation. -/
theorem loop_exec {w stop output : ℕ} (original : ℕ → ℤ) (values : ℕ → ℤ)
    (parameters : Fin (k+5) → ℤ)
    (addressFits : ∀ i, i<stop → Fits w (output+i : ℕ))
    (nextFits : ∀ i, i<stop → Fits w (i+1 : ℕ))
    (contract : ∀ i, i<stop → ∀ current : Data e.registers,
      Controls e current i stop output → current.2=prefixMemory original output values i →
      (∀ j : Fin (k+5), 5≤ j.val → current.1 (reg e j)=parameters j) →
      e.Safe w (fun j => current.1 (reg e j)) current.2 ∧
        e.eval (fun j => current.1 (reg e j)) current.2=values i ∧ Fits w (values i)) :
    ∀ remaining start, start+remaining=stop → ∀ data : Data e.registers,
      Controls e data start stop output → data.2=prefixMemory original output values start →
      (∀ j : Fin (k+5), 5≤ j.val → data.1 (reg e j)=parameters j) →
      ∃ result, Structured.Exec w (program e) data result ((e.nodes+5)*remaining+2) ∧
        Controls e result stop stop output ∧ result.2=prefixMemory original output values stop ∧
        ∀ j : Fin (k+5), 5≤ j.val → result.1 (reg e j)=parameters j := by
  intro remaining
  induction remaining with
  | zero =>
    intro start equality data controls memory params
    have equal : start=stop := by omega
    subst start
    refine ⟨data,?_,controls,memory,params⟩
    have done : ¬(Structured.Condition.lt (index e) (length e)).Holds data := by
      simp only [Structured.Condition.Holds,controls.1,controls.2.1]
      omega
    simpa only [program,Nat.mul_zero,Nat.zero_add] using
      (Structured.Exec.loop_done (body := body e) done)
  | succ remaining ih =>
    intro start equality data controls memory params
    have small : start<stop := by omega
    obtain ⟨safe,value,fits⟩ := contract start small data controls memory params
    obtain ⟨middle,execution,middleControls,middleMemory,middleParameters⟩ :=
      body_exec e data controls safe (addressFits start small) (nextFits start small) (by simpa only [value] using fits)
    have nextMemory : middle.2=prefixMemory original output values (start+1) := by
      rw [middleMemory,value,memory,← prefixMemory_succ]
    have nextParameters : ∀ j : Fin (k+5), 5≤ j.val → middle.1 (reg e j)=parameters j := by
      intro j hj
      rw [middleParameters j hj]
      exact params j hj
    obtain ⟨result,rest,finalControls,finalMemory,finalParameters⟩ :=
      ih (start+1) (by omega) middle middleControls nextMemory nextParameters
    have more : (Structured.Condition.lt (index e) (length e)).Holds data := by
      simp only [Structured.Condition.Holds,controls.1,controls.2.1]
      exact_mod_cast small
    refine ⟨result,?_,finalControls,finalMemory,finalParameters⟩
    have total := Structured.Exec.loop_more more execution rest
    have count : e.nodes+3+((e.nodes+5)*remaining+2)+2=(e.nodes+5)*(remaining+1)+2 := by ring
    simpa only [program,Nat.succ_eq_add_one,count] using total

end Table
end LeanTrominoes.ImplicationGraph.TwoSATExpression

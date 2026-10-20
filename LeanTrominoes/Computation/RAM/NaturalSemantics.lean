/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalArithmetic
import LeanTrominoes.Computation.RAM.RegisterFrame

/-! # Bounded natural-state certificates for ordinary word-RAM instructions

Every subtraction must be nonnegative, every written word and dereferenced
address must stay within the natural bound. The refinement theorem proves
all checks of the original signed bounded-word RAM, with the same instruction
count. This is proof notation, not a machine-model extension.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Natural
variable {r : Nat}

inductive Step (bound : Nat) : Structured.Primitive r → NaturalData r → NaturalData r → Prop
  | constant (data : NaturalData r) (dst : Fin r) (value : Nat) : value≤bound →
      Step bound (.constant dst value) data (data.set dst value)
  | copy (data : NaturalData r) (dst src : Fin r) : data.1 src≤bound →
      Step bound (.copy dst src) data (data.set dst (data.1 src))
  | add (data : NaturalData r) (dst a b : Fin r) : data.1 a+data.1 b≤bound →
      Step bound (.arithmetic .add dst a b) data (data.set dst (data.1 a+data.1 b))
  | sub (data : NaturalData r) (dst a b : Fin r) : data.1 b≤data.1 a → data.1 a-data.1 b≤bound →
      Step bound (.arithmetic .sub dst a b) data (data.set dst (data.1 a-data.1 b))
  | mul (data : NaturalData r) (dst a b : Fin r) : data.1 a*data.1 b≤bound →
      Step bound (.arithmetic .mul dst a b) data (data.set dst (data.1 a*data.1 b))
  | div (data : NaturalData r) (dst a b : Fin r) : data.1 a/data.1 b≤bound →
      Step bound (.arithmetic .div dst a b) data (data.set dst (data.1 a/data.1 b))
  | mod (data : NaturalData r) (dst a b : Fin r) : data.1 a%data.1 b≤bound →
      Step bound (.arithmetic .mod dst a b) data (data.set dst (data.1 a%data.1 b))
  | load (data : NaturalData r) (dst address : Fin r) : data.1 address≤bound → data.2 (data.1 address)≤bound →
      Step bound (.load dst address) data (data.set dst (data.2 (data.1 address)))
  | store (data : NaturalData r) (address src : Fin r) : data.1 address≤bound → data.1 src≤bound →
      Step bound (.store address src) data (data.store (data.1 address) (data.1 src))

def Holds (condition : Structured.Condition r) (data : NaturalData r) : Prop :=
  match condition with
  | .eq a b => data.1 a=data.1 b
  | .lt a b => data.1 a<data.1 b

instance (condition : Structured.Condition r) (data : NaturalData r) : Decidable (Holds condition data) :=
  match condition with
  | .eq a b => inferInstanceAs (Decidable (data.1 a=data.1 b))
  | .lt a b => inferInstanceAs (Decidable (data.1 a<data.1 b))

theorem holds_word (condition : Structured.Condition r) (data : NaturalData r) :
    Holds condition data ↔ condition.Holds data.word := by
  cases condition <;> simp [Holds,Structured.Condition.Holds,NaturalData.word]

inductive Exec (bound : Nat) : Structured.Code r → NaturalData r → NaturalData r → Nat → Prop
  | atom {op data result} : Step bound op data result → Exec bound (.atom op) data result 1
  | seq {a b data middle result n m} : Exec bound a data middle n → Exec bound b middle result m →
      Exec bound (.seq a b) data result (n+m)
  | branch_yes {c yes no data result n} : Holds c data → Exec bound yes data result n →
      Exec bound (.branch c yes no) data result (n+1)
  | branch_no {c yes no data result n} : ¬Holds c data → Exec bound no data result n →
      Exec bound (.branch c yes no) data result (n+2)
  | loop_done {c body data} : ¬Holds c data → Exec bound (.loop c body) data data 2
  | loop_more {c body data middle result n m} : Holds c data → Exec bound body data middle n →
      Exec bound (.loop c body) middle result m → Exec bound (.loop c body) data result (n+m+2)

theorem Step.compiles {bound w : Nat} {op : Structured.Primitive r} {data result : NaturalData r}
    (execution : Step bound op data result) (width : Fits w bound) :
    Structured.Exec w (.atom op) data.word result.word 1 := by
  cases execution with
  | constant data dst value bounded => exact NaturalData.constant_exec data dst value (Allocation.nat_fits_le width bounded)
  | copy data dst src bounded => exact NaturalData.copy_exec data dst src (Allocation.nat_fits_le width bounded)
  | add data dst a b bounded => exact NaturalData.add_exec data dst a b (Allocation.nat_fits_le width bounded)
  | sub data dst a b nonnegative bounded => exact NaturalData.sub_exec data dst a b nonnegative (Allocation.nat_fits_le width bounded)
  | mul data dst a b bounded => exact NaturalData.mul_exec data dst a b (Allocation.nat_fits_le width bounded)
  | div data dst a b bounded => exact NaturalData.div_exec data dst a b (Allocation.nat_fits_le width bounded)
  | mod data dst a b bounded => exact NaturalData.mod_exec data dst a b (Allocation.nat_fits_le width bounded)
  | load data dst address addressBound valueBound =>
      exact NaturalData.load_exec data dst address
        (Allocation.nat_fits_le width addressBound) (Allocation.nat_fits_le width valueBound)
  | store data address src addressBound valueBound =>
      exact NaturalData.store_exec data address src
        (Allocation.nat_fits_le width addressBound) (Allocation.nat_fits_le width valueBound)

theorem Exec.compiles {bound w : Nat} {code : Structured.Code r} {data result : NaturalData r} {cost : Nat}
    (execution : Exec bound code data result cost) (width : Fits w bound) :
    NaturalData.Exec w code data result cost := by
  induction execution with
  | atom execution => exact execution.compiles width
  | seq _ _ a b => exact a.seq b
  | branch_yes condition _ ih => exact Structured.Exec.branch_yes ((holds_word ..).mp condition) ih
  | branch_no condition _ ih => exact Structured.Exec.branch_no (fun h => condition ((holds_word ..).mpr h)) ih
  | loop_done condition => exact Structured.Exec.loop_done (fun h => condition ((holds_word ..).mpr h))
  | loop_more condition _ _ a b => exact Structured.Exec.loop_more ((holds_word ..).mp condition) a b

theorem Step.bounded {bound : Nat} {op : Structured.Primitive r} {data result : NaturalData r}
    (execution : Step bound op data result) (before : NaturalData.Bounded bound data) : NaturalData.Bounded bound result := by
  cases execution <;> first | apply before.set; assumption | apply before.store; assumption

theorem Exec.bounded {bound : Nat} {code : Structured.Code r} {data result : NaturalData r} {cost : Nat}
    (execution : Exec bound code data result cost) (before : NaturalData.Bounded bound data) : NaturalData.Bounded bound result := by
  induction execution with
  | atom execution => exact execution.bounded before
  | seq _ _ a b => exact b (a before)
  | branch_yes _ _ ih => exact ih before
  | branch_no _ _ ih => exact ih before
  | loop_done _ => exact before
  | loop_more _ _ _ a b => exact b (a before)

/-- A finite iteration certificate includes both branch tests and back jumps.
The state family is proof data, while `body` remains ordinary RAM code. -/
theorem Exec.finite_loop {bound limit budget : Nat} (condition : Structured.Condition r)
    (body : Structured.Code r) (states : Nat → NaturalData r)
    (continues : ∀ k, k<limit → Holds condition (states k))
    (stops : ¬Holds condition (states limit))
    (steps : ∀ k, k<limit → ∃ cost, Exec bound body (states k) (states (k+1)) cost ∧ cost≤budget) :
    ∃ cost, Exec bound (.loop condition body) (states 0) (states limit) cost ∧
      cost≤(budget+2)*limit+2 := by
  induction limit generalizing states with
  | zero => exact ⟨2,Exec.loop_done stops,by omega⟩
  | succ limit ih =>
    obtain ⟨first,firstExec,firstBound⟩ := steps 0 (by omega)
    obtain ⟨later,laterExec,laterBound⟩ := ih (fun k => states (k+1))
      (fun k hk => continues (k+1) (by omega)) stops (fun k hk => steps (k+1) (by omega))
    refine ⟨first+later+2,Exec.loop_more (continues 0 (by omega)) firstExec laterExec,?_⟩
    simp only [Nat.mul_add,Nat.mul_one]
    omega

theorem Step.register_eq {bound : Nat} {op : Structured.Primitive r} {data result : NaturalData r}
    (execution : Step bound op data result) {i : Fin r} (untouched : op.PreservesRegister i) :
    result.1 i=data.1 i := by
  cases execution <;> simp_all [Structured.Primitive.PreservesRegister,NaturalData.set,NaturalData.store]

theorem Exec.register_eq {bound : Nat} {code : Structured.Code r} {data result : NaturalData r} {cost : Nat}
    (execution : Exec bound code data result cost) {i : Fin r} (untouched : code.PreservesRegister i) :
    result.1 i=data.1 i := by
  induction execution with
  | atom execution => exact execution.register_eq untouched
  | seq _ _ a b => exact (b untouched.2).trans (a untouched.1)
  | branch_yes _ _ ih => exact ih untouched.1
  | branch_no _ _ ih => exact ih untouched.2
  | loop_done _ => rfl
  | loop_more _ _ _ a b => exact (b untouched).trans (a untouched)

end LeanTrominoes.ComplexityAbstract.RAM.Natural

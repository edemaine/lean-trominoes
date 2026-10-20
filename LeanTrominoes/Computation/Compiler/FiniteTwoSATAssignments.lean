/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBudgets

/-! # Fixed arithmetic assignments with a shared scratch-register bank

A list of assignments compiles to ordinary word instructions. The expression
size fixes the scratch bank and instruction count independently of the input.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

structure Assignment (k : ℕ) where
  destination : Fin k
  expression : Expr k

namespace Assignment
variable {k capacity w : ℕ}

def inputRegister (capacity : ℕ) : Fin k → Fin (k+capacity) := Fin.castAdd capacity

def temporary (k capacity : ℕ) (positive : 0<capacity) (j : ℕ) : Fin (k+capacity) :=
  ⟨k+j%capacity,by have := Nat.mod_lt j positive; omega⟩

def code (a : Assignment k) (capacity : ℕ) (positive : 0<capacity) : Structured.Code (k+capacity) :=
  .seq (a.expression.code (inputRegister capacity) (temporary k capacity positive) 0)
    (.atom (.copy (inputRegister capacity a.destination) (temporary k capacity positive 0)))

def update (a : Assignment k) (env : Fin k → ℤ) (memory : ℕ → ℤ) : Fin k → ℤ :=
  Function.update env a.destination (a.expression.eval env memory)

theorem exec (a : Assignment k) (positive : 0<capacity) (small : a.expression.nodes≤capacity)
    (env : Fin k → ℤ) (data : Data (k+capacity))
    (inputs : ∀ i, data.1 (inputRegister capacity i)=env i)
    (safe : a.expression.Safe w env data.2) :
    ∃ result, Structured.Exec w (a.code capacity positive) data result (a.expression.nodes+1) ∧
      result.2=data.2 ∧ ∀ i, result.1 (inputRegister capacity i)=a.update env data.2 i := by
  have tempValue (j : ℕ) (hj : j<a.expression.nodes) :
      (temporary k capacity positive j).val=k+j := by
    simp [temporary,Nat.mod_eq_of_lt (show j<capacity by omega)]
  have fresh : ∀ i, Outside (temporary k capacity positive) 0 a.expression.nodes (inputRegister capacity i) := by
    intro i j lo hi equal
    have h := congrArg Fin.val equal
    simp only [inputRegister,Fin.val_castAdd,tempValue j (by omega)] at h
    have := i.isLt
    omega
  obtain ⟨middle,run,mem,value,preserved⟩ := a.expression.exec (inputRegister capacity)
    (temporary k capacity positive) 0 env data inputs fresh (by
      intro i ilo ihi j jlo jhi equal
      have h := congrArg Fin.val equal
      simpa only [tempValue i (by omega),tempValue j (by omega),Nat.add_left_cancel_iff] using h) safe
  have fits : Fits w (a.expression.eval env data.2) :=
    a.expression.safe_result env data.2 safe
  have copy : Structured.Exec w (.atom (.copy (inputRegister capacity a.destination)
      (temporary k capacity positive 0))) middle
      (Function.update middle.1 (inputRegister capacity a.destination)
        (a.expression.eval env data.2),middle.2) 1 := by
    apply Structured.Exec.atom
    simp only [Structured.Primitive.eval,value,fits,ite_true]
  refine ⟨_,run.seq copy,mem,?_⟩
  intro i
  simp only [update,Function.update_apply]
  by_cases equal : i=a.destination
  · subst i
    simp
  · have different : inputRegister capacity i≠inputRegister capacity a.destination := by
      intro same
      apply equal
      have values := congrArg (fun j : Fin (k+capacity) => j.val) same
      exact Fin.ext values
    rw [ite_eq_right different,ite_eq_right equal,preserved _ (fresh i),inputs]

def evaluate : List (Assignment k) → (Fin k → ℤ) → (ℕ → ℤ) → (Fin k → ℤ)
  | [],env,_ => env
  | a::rest,env,memory => evaluate rest (a.update env memory) memory

def sequence (capacity : ℕ) (positive : 0<capacity) (scratch : Fin k) :
    List (Assignment k) → Structured.Code (k+capacity)
  | [] => .atom (.copy (inputRegister capacity scratch) (inputRegister capacity scratch))
  | a::rest => .seq (a.code capacity positive) (sequence capacity positive scratch rest)

def cost : List (Assignment k) → ℕ
  | [] => 1
  | a::rest => a.expression.nodes+1+cost rest

def Safe (w : ℕ) (scratch : Fin k) : List (Assignment k) → (Fin k → ℤ) → (ℕ → ℤ) → Prop
  | [],env,_ => Fits w (env scratch)
  | a::rest,env,memory => a.expression.Safe w env memory ∧ Safe w scratch rest (a.update env memory) memory

theorem sequence_exec (assignments : List (Assignment k)) (positive : 0<capacity)
    (small : ∀ a∈assignments, a.expression.nodes≤capacity) (scratch : Fin k)
    (env : Fin k → ℤ) (data : Data (k+capacity))
    (inputs : ∀ i, data.1 (inputRegister capacity i)=env i)
    (safe : Safe w scratch assignments env data.2) :
    ∃ result, Structured.Exec w (sequence capacity positive scratch assignments) data result (cost assignments) ∧
      result.2=data.2 ∧ ∀ i, result.1 (inputRegister capacity i)=evaluate assignments env data.2 i := by
  induction assignments generalizing env data with
  | nil =>
    refine ⟨data,?_,rfl,inputs⟩
    apply Structured.Exec.atom
    have fixed : Function.update data.1 (inputRegister capacity scratch) (data.1 (inputRegister capacity scratch))=data.1 :=
      Function.update_eq_self _ _
    have fits : Fits w (data.1 (inputRegister capacity scratch)) := by
      rw [inputs]; exact safe
    simp only [Structured.Primitive.eval,fits,ite_true,fixed]
  | cons a rest ih =>
    obtain ⟨middle,run,memory,values⟩ := a.exec positive (small a (by simp)) env data inputs safe.1
    obtain ⟨result,remaining,finalMemory,finalValues⟩ := ih (by intro b hb; exact small b (by simp [hb]))
      (a.update env data.2) middle values (by simpa only [memory] using safe.2)
    exact ⟨result,run.seq remaining,finalMemory.trans memory,by simpa only [evaluate,memory] using finalValues⟩

end Assignment
end LeanTrominoes.ImplicationGraph.TwoSATExpression

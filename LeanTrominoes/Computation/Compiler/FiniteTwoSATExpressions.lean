/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.StructuredCompile

/-! # Arithmetic and memory expressions compiled to ordinary RAM instructions

The compiler reserves one register per expression node. Every arithmetic
operation and load remains one checked primitive instruction. This is used for
pointwise table generation; it does not introduce an evaluator instruction.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

inductive Expr (k : ℕ)
  | constant (value : ℤ)
  | inputValue (index : Fin k)
  | load (address : Expr k)
  | arithmetic (op : Arithmetic) (left right : Expr k)

def Expr.eval {k : ℕ} (env : Fin k → ℤ) (memory : ℕ → ℤ) : Expr k → ℤ
  | .constant value => value
  | .inputValue index => env index
  | .load address => memory (address.eval env memory).toNat
  | .arithmetic op left right => op.eval (left.eval env memory) (right.eval env memory)

def Expr.nodes {k : ℕ} : Expr k → ℕ
  | .constant _ | .inputValue _ => 1
  | .load address => address.nodes+1
  | .arithmetic _ left right => left.nodes+right.nodes+1

theorem Expr.nodes_positive {k : ℕ} (e : Expr k) : 0<e.nodes := by cases e <;> simp [Expr.nodes]

def Expr.Safe {k : ℕ} (w : ℕ) (env : Fin k → ℤ) (memory : ℕ → ℤ) : Expr k → Prop
  | .constant value => Fits w value
  | .inputValue index => Fits w (env index)
  | .load address => address.Safe w env memory ∧ 0≤address.eval env memory ∧
      address.eval env memory<(2^w : ℕ) ∧ Fits w (memory (address.eval env memory).toNat)
  | .arithmetic op left right => left.Safe w env memory ∧ right.Safe w env memory ∧
      Fits w (op.eval (left.eval env memory) (right.eval env memory))

def Expr.code {k r : ℕ} (input : Fin k → Fin r) (temporary : ℕ → Fin r) : Expr k → ℕ → Structured.Code r
  | .constant value, start => .atom (.constant (temporary start) value)
  | .inputValue index, start => .atom (.copy (temporary start) (input index))
  | .load address, start => .seq (address.code input temporary start) (.atom (.load (temporary start) (temporary start)))
  | .arithmetic op left right, start =>
    .seq (left.code input temporary start)
      (.seq (right.code input temporary (start+left.nodes))
        (.atom (.arithmetic op (temporary start) (temporary start) (temporary (start+left.nodes)))))

def Outside {r : ℕ} (temporary : ℕ → Fin r) (start count : ℕ) (reg : Fin r) : Prop :=
  ∀ j, start≤ j → j<start+count → reg≠temporary j

def set {r : ℕ} (data : Data r) (reg : Fin r) (value : ℤ) : Data r :=
  (Function.update data.1 reg value,data.2)

theorem set_preserves {r start count : ℕ} (data : Data r) (temporary : ℕ → Fin r) (value : ℤ)
    (positive : 0<count) :
    ∀ reg, Outside temporary start count reg → (set data (temporary start) value).1 reg=data.1 reg := by
  intro reg outside
  simp only [set,Function.update_of_ne (outside start (by omega) (by omega))]

/-- Compiling an expression preserves memory and all registers outside its
reserved interval, and takes exactly one primitive instruction per node. -/
theorem Expr.exec {k r w : ℕ} (e : Expr k) (input : Fin k → Fin r) (temporary : ℕ → Fin r)
    (start : ℕ) (env : Fin k → ℤ) (data : Data r)
    (inputs : ∀ i, data.1 (input i)=env i)
    (fresh : ∀ i, Outside temporary start e.nodes (input i))
    (injective : ∀ i, start≤ i → i<start+e.nodes → ∀ j, start≤ j → j<start+e.nodes →
      temporary i=temporary j → i=j)
    (safe : e.Safe w env data.2) :
    ∃ result, Structured.Exec w (e.code input temporary start) data result e.nodes ∧
      result.2=data.2 ∧ result.1 (temporary start)=e.eval env data.2 ∧
      ∀ reg, Outside temporary start e.nodes reg → result.1 reg=data.1 reg := by
  induction e generalizing start data with
  | constant value =>
    simp only [Safe] at safe
    refine ⟨set data (temporary start) value,?_,rfl,?_,set_preserves data temporary value (by simp [nodes])⟩
    · apply Structured.Exec.atom
      simp only [Structured.Primitive.eval,safe,ite_true,set]
    · simp [set,eval]
  | inputValue index =>
    simp only [Safe] at safe
    refine ⟨set data (temporary start) (env index),?_,rfl,?_,set_preserves data temporary _ (by simp [nodes])⟩
    · apply Structured.Exec.atom
      simp only [Structured.Primitive.eval,inputs,safe,ite_true,set]
    · simp [set,eval]
  | load address ih =>
    simp only [Safe] at safe
    obtain ⟨middle,execution,memory,value,preserved⟩ := ih start data inputs
      (fun i j lo hi => fresh i j lo (by simp only [nodes] at *; omega))
      (fun i ilo ihi j jlo jhi equal => injective i ilo (by simp only [nodes]; omega) j jlo
        (by simp only [nodes]; omega) equal) safe.1
    have op : Structured.Exec w (.atom (.load (temporary start) (temporary start))) middle
        (set middle (temporary start) (data.2 (address.eval env data.2).toNat)) 1 := by
      apply Structured.Exec.atom
      have bounds : ¬ (middle.1 (temporary start)<0 ∨ middle.1 (temporary start)≥(2^w : ℕ)) := by
        rw [value]
        exact not_or.mpr ⟨not_lt.mpr safe.2.1,not_le.mpr safe.2.2.1⟩
      rw [value] at bounds
      simp only [Structured.Primitive.eval,value,bounds,ite_false,memory,safe.2.2.2,ite_true,set]
    refine ⟨_,by simpa only [code,nodes] using execution.seq op,?_,?_,?_⟩
    · exact memory
    · simp [set,eval]
    · intro reg outside
      rw [show (set middle (temporary start) _).1 reg=middle.1 reg by
        simp [set,Function.update_of_ne (outside start (by omega) (by simp [nodes]))]]
      apply preserved reg
      intro j lo hi
      exact outside j lo (by simp only [nodes]; omega)
  | arithmetic op left right leftIH rightIH =>
    simp only [Safe] at safe
    obtain ⟨middle,leftExec,leftMemory,leftValue,leftPreserved⟩ := leftIH start data inputs
      (fun i j lo hi => fresh i j lo (by simp only [nodes] at *; omega))
      (fun i ilo ihi j jlo jhi equal => injective i ilo (by simp only [nodes]; omega) j jlo
        (by simp only [nodes]; omega) equal) safe.1
    have middleInputs : ∀ i, middle.1 (input i)=env i := by
      intro i
      rw [leftPreserved (input i) (fun j lo hi => fresh i j lo (by simp only [nodes]; omega))]
      exact inputs i
    obtain ⟨last,rightExec,rightMemory,rightValue,rightPreserved⟩ := rightIH (start+left.nodes) middle middleInputs
      (fun i j lo hi => fresh i j (by omega) (by simp only [nodes]; omega))
      (fun i ilo ihi j jlo jhi equal => injective i (by omega) (by simp only [nodes]; omega) j
        (by omega) (by simp only [nodes]; omega) equal) (by simpa only [leftMemory] using safe.2.1)
    have leftKept : last.1 (temporary start)=left.eval env data.2 := by
      rw [rightPreserved (temporary start),leftValue]
      intro j lo hi equal
      have distinct := injective start (by omega) (by have := left.nodes_positive; simp only [nodes]; omega)
        j (by omega) (by simp only [nodes]; omega) equal
      have positive := left.nodes_positive
      omega
    have rightKept : last.1 (temporary (start+left.nodes))=right.eval env data.2 := by
      simpa only [leftMemory] using rightValue
    have arithmeticExec : Structured.Exec w
        (.atom (.arithmetic op (temporary start) (temporary start) (temporary (start+left.nodes)))) last
        (set last (temporary start) (op.eval (left.eval env data.2) (right.eval env data.2))) 1 := by
      apply Structured.Exec.atom
      simp only [Structured.Primitive.eval,leftKept,rightKept,safe.2.2,ite_true,set]
    refine ⟨_,by simpa only [code,nodes,Nat.add_assoc] using leftExec.seq (rightExec.seq arithmeticExec),?_,?_,?_⟩
    · exact rightMemory.trans leftMemory
    · simp [set,eval]
    · intro reg outside
      rw [show (set last (temporary start) _).1 reg=last.1 reg by
        simp [set,Function.update_of_ne (outside start (by omega) (by simp only [nodes]; have := left.nodes_positive; omega))]]
      rw [rightPreserved reg (fun j lo hi => outside j (by omega) (by simp only [nodes]; omega))]
      apply leftPreserved reg
      intro j lo hi
      exact outside j lo (by simp only [nodes]; omega)

def Expr.registers {k : ℕ} (e : Expr k) : ℕ := k+e.nodes

def Expr.inputRegister {k : ℕ} (e : Expr k) : Fin k → Fin e.registers := Fin.castAdd e.nodes

def Expr.temporary {k : ℕ} (e : Expr k) (j : ℕ) : Fin e.registers :=
  ⟨k+j%e.nodes,by dsimp [registers]; have := Nat.mod_lt j e.nodes_positive; omega⟩

def Expr.program {k : ℕ} (e : Expr k) : Structured.Code e.registers :=
  e.code e.inputRegister e.temporary 0

theorem Expr.temporary_val {k : ℕ} (e : Expr k) (j : ℕ) (small : j<e.nodes) :
    (e.temporary j).val=k+j := by simp [temporary,Nat.mod_eq_of_lt small]

/-- The compiler chooses a concrete finite register bank. Its register count
and instruction sequence depend only on the expression, never on the input. -/
theorem Expr.program_exec {k w : ℕ} (e : Expr k) (env : Fin k → ℤ) (data : Data e.registers)
    (inputs : ∀ i, data.1 (e.inputRegister i)=env i) (safe : e.Safe w env data.2) :
    ∃ result, Structured.Exec w e.program data result e.nodes ∧ result.2=data.2 ∧
      result.1 (e.temporary 0)=e.eval env data.2 ∧
      ∀ i, result.1 (e.inputRegister i)=data.1 (e.inputRegister i) := by
  obtain ⟨result,execution,memory,value,preserved⟩ := e.exec e.inputRegister e.temporary 0 env data inputs
    (by
      intro i j lo hi equal
      have h := congrArg Fin.val equal
      rw [e.temporary_val j (by omega)] at h
      simp only [inputRegister,Fin.val_castAdd] at h
      omega)
    (by
      intro i ilo ihi j jlo jhi equal
      have h := congrArg Fin.val equal
      rw [e.temporary_val i (by omega),e.temporary_val j (by omega)] at h
      omega) safe
  refine ⟨result,execution,memory,value,?_⟩
  intro i
  apply preserved
  intro j lo hi equal
  have h := congrArg Fin.val equal
  rw [e.temporary_val j (by omega)] at h
  simp only [inputRegister,Fin.val_castAdd] at h
  omega

end LeanTrominoes.ImplicationGraph.TwoSATExpression

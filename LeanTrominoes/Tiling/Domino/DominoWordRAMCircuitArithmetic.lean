/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMMultiplication
import LeanTrominoes.Tiling.Domino.DominoWordRAMSubtraction
import LeanTrominoes.Computation.RAM.NaturalEmbedding
import Mathlib.Data.ZMod.Basic

/-! # Arithmetic nodes for binary integer circuits

Each circuit node uses a fresh binary output array. Checked addition,
subtraction, and multiplication implement the corresponding ring operation
modulo the common precision. Interpreted integers never become RAM words.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

inductive Operation | add | sub | mul

def Operation.code : Operation → Binary.Code
  | .add => addProgram
  | .sub => borrowProgram
  | .mul => Multiply.program

def Operation.eval {R : Type} [Ring R] : Operation → R → R → R
  | .add => fun a b => a+b
  | .sub => fun a b => a-b
  | .mul => fun a b => a*b

def arrayLayout (p : Multiply.Layout) : Binary.Layout where
  first := p.first
  second := p.second
  output := p.output
  length := p.length
  first_disjoint := by intro i hi j hj _; exact p.first_disjoint i hi j hj
  second_disjoint := by intro i hi j hj _; exact p.second_disjoint i hi j hj

structure Result (op : Operation) (p : Multiply.Layout) (source : ℕ → ℕ) (data : Binary.Data) : Prop where
  length : data.1 Reg.length=p.length
  output : data.1 Reg.output=p.output
  bits : ∀ i< p.length, data.2 (p.output+i)≤1
  frame : ∀ address, (address< p.output ∨ p.output+p.length≤address) → data.2 address=source address
  value : (Binary.value data.2 p.output p.length : ZMod (2^p.length))=
    op.eval (Binary.value source p.first p.length : ZMod (2^p.length))
      (Binary.value source p.second p.length : ZMod (2^p.length))

/-- One arithmetic node is an actual bounded-word execution with a uniform
quadratic budget in binary precision and an exact external-memory frame. -/
theorem operation_exec {w : ℕ} (op : Operation) (p : Multiply.Layout) (data : Binary.Data)
    (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (output : data.1 Reg.output=p.output) (length : data.1 Reg.length=p.length)
    (firstBits : ∀ i< p.length, data.2 (p.first+i)≤1)
    (secondBits : ∀ i< p.length, data.2 (p.second+i)≤1)
    (zero : ∀ i< p.length, data.2 (p.output+i)=0)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w op.code data result cost ∧
      cost≤26*p.length^2+26*p.length+7 ∧ Result op p data.2 result := by
  cases op with
  | add =>
    obtain ⟨result,run,correct⟩ := addProgram_exec (arrayLayout p) data length first second output
      firstBits secondBits small firstFits secondFits outputFits lengthFits
    refine ⟨result,13*p.length+6,run,by nlinarith,correct.length,correct.output,
      correct.output_bits,correct.frame,?_⟩
    have equality := congrArg (fun n : ℕ => (n : ZMod (2^p.length))) correct.result
    simpa only [arrayLayout,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero,Operation.eval] using equality
  | sub =>
    obtain ⟨result,run,correct⟩ := borrowProgram_exec (arrayLayout p) data length first second output
      firstBits secondBits small firstFits secondFits outputFits lengthFits
    refine ⟨result,15*p.length+6,run,by nlinarith,correct.length,correct.output,
      correct.output_bits,correct.frame,?_⟩
    have equality := congrArg (fun n : ℕ => (n : ZMod (2^p.length))) correct.result
    have reduced : (Binary.value result.2 p.output p.length : ZMod (2^p.length))+
        (Binary.value data.2 p.second p.length : ZMod (2^p.length))=
        (Binary.value data.2 p.first p.length : ZMod (2^p.length)) := by
      simpa only [arrayLayout,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using equality
    exact eq_sub_iff_add_eq.mpr reduced
  | mul =>
    obtain ⟨result,cost,run,bound,correct,value⟩ := Multiply.program_exec p data first second output length
      firstBits secondBits zero small firstFits secondFits outputFits lengthFits
    refine ⟨result,cost,run,bound,correct.length,correct.output,correct.output_bits,correct.frame,?_⟩
    rw [value]
    simp [Operation.eval]

theorem operation_size (op : Operation) : op.code.size<128 := by
  cases op <;> decide

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

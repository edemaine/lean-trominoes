/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitConstants

/-! # One instruction in a fixed binary arithmetic circuit

Circuit instructions are expanded into ordinary RAM programs; they are not
additional primitive operations of the machine.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

inductive Node
  | constant (bit : Bool)
  | arithmetic (op : Operation) (first second : ℕ)

def Node.Valid (output : ℕ) : Node → Prop
  | .constant _ => True
  | .arithmetic _ first second => first< output ∧ second< output

def Node.eval {R : Type} [Ring R] (values : ℕ → R) : Node → R
  | .constant bit => (bitValue bit : R)
  | .arithmetic op first second => op.eval (values first) (values second)

def Node.program (output : ℕ) : Node → Code
  | .constant bit => constantProgram bit output
  | .arithmetic op first second => arithmeticProgram op first second output

structure StepResult (node : Node) (base length output : ℕ) (source : ℕ → ℕ) (data : Data) : Prop where
  base_eq : data.1 baseRegister=base
  length_eq : data.1 (low Reg.length)=length
  bits : ∀ i< length, data.2 (slotBase base length output+i)≤1
  frame : ∀ address, (address< slotBase base length output ∨ slotBase base length output+length≤address) →
    data.2 address=source address
  value : (Binary.value data.2 (slotBase base length output) length : ZMod (2^length))=
    node.eval (fun slot => (Binary.value source (slotBase base length slot) length : ZMod (2^length)))

/-- Each valid circuit instruction has a fixed checked RAM expansion. -/
theorem node_exec {w base length slots output : ℕ} (node : Node) (data : Data)
    (baseEq : data.1 baseRegister=base) (lengthEq : data.1 (low Reg.length)=length)
    (positive : 0< length) (outputBound : output≤slots) (valid : node.Valid output)
    (known : ∀ slot< output, ∀ i< length, data.2 (slotBase base length slot+i)≤1)
    (zero : ∀ i< length, data.2 (slotBase base length output+i)=0)
    (fits : Fits w (resourceBound base length slots)) :
    ∃ result cost, NaturalData.Exec w (node.program output) data result cost ∧
      cost≤26*length^2+26*length+16 ∧ StepResult node base length output data.2 result := by
  cases node with
  | constant bit =>
    obtain ⟨run,correct⟩ := constant_exec bit data output baseEq lengthEq positive outputBound zero fits
    refine ⟨constantState data bit output,5,run,by nlinarith,
      correct.base_eq,correct.length_eq,correct.bits,correct.frame,?_⟩
    rw [correct.value]
    rfl
  | arithmetic op first second =>
    obtain ⟨result,cost,run,bound,correct⟩ := arithmetic_exec op data first second output baseEq lengthEq
      (by have := valid.1; omega) (by have := valid.2; omega) outputBound
      (by have := valid.1; omega) (by have := valid.2; omega)
      (known first valid.1) (known second valid.2) zero fits
    exact ⟨result,cost,run,bound,correct.base_eq,correct.length_eq,correct.bits,correct.frame,correct.value⟩

def Node.advance {R : Type} [Ring R] (node : Node) (output : ℕ) (values : ℕ → R) : ℕ → R :=
  Function.update values output (node.eval values)

theorem Node.eval_congr {R : Type} [Ring R] {node : Node} {output : ℕ} {first second : ℕ → R}
    (valid : node.Valid output) (same : ∀ i< output, first i=second i) :
    node.eval first=node.eval second := by
  cases node with
  | constant bit => rfl
  | arithmetic op a b => simp only [Node.eval,same a valid.1,same b valid.2]

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

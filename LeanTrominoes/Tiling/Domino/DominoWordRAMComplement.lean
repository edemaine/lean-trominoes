/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition

/-! # Checked binary complementation

Complementing an arbitrary precision integer is a linear-time loop over its
binary digits. Exact in-place complementation is supported.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

attribute [local simp] Reg.index Reg.length Reg.first Reg.output Reg.left Reg.one Reg.address
  NaturalData.set NaturalData.store

def complementBody : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.arithmetic .sub Reg.left Reg.one Reg.left)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) <|
  .seq (.atom (.store Reg.address Reg.left))
       (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def complement1 (data : Data) := data.set Reg.address (data.1 Reg.first+data.1 Reg.index)
def complement2 (data : Data) := (complement1 data).set Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index))
def complement3 (data : Data) := (complement2 data).set Reg.left ((complement2 data).1 Reg.one-(complement2 data).1 Reg.left)
def complement4 (data : Data) := (complement3 data).set Reg.address (data.1 Reg.output+data.1 Reg.index)
def complement5 (data : Data) := (complement4 data).store ((complement4 data).1 Reg.address) ((complement4 data).1 Reg.left)
def complementStep (data : Data) := (complement5 data).set Reg.index ((complement5 data).1 Reg.index+(complement5 data).1 Reg.one)

attribute [local simp] complement1 complement2 complement3 complement4 complement5 complementStep

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem complementStep_registers (data : Data) :
    (complementStep data).1=Function.update
      (Function.update (Function.update data.1 Reg.left
        (data.1 Reg.one-data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.address (data.1 Reg.output+data.1 Reg.index))
        Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;> simp

theorem complementStep_memory (data : Data) :
    (complementStep data).2=Function.update data.2 (data.1 Reg.output+data.1 Reg.index)
      (data.1 Reg.one-data.2 (data.1 Reg.first+data.1 Reg.index)) := by simp

/-- Six ordinary instructions complement and store one input bit. -/
theorem complementBody_exec {w : ℕ} (data : Data) (one : data.1 Reg.one=1)
    (bit : data.2 (data.1 Reg.first+data.1 Reg.index)≤1)
    (small : Fits w (1:ℕ))
    (source : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (destination : Fits w (data.1 Reg.output+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    NaturalData.Exec w complementBody data (complementStep data) 6 := by
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index source
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (complement1 data) (complement2 data) 1 := by
    simpa using NaturalData.load_exec (complement1 data) Reg.left Reg.address
      (by simpa using source) (by simpa using fits_le small bit)
  have h3 : NaturalData.Exec w (.atom (.arithmetic .sub Reg.left Reg.one Reg.left)) (complement2 data) (complement3 data) 1 := by
    apply NaturalData.sub_exec
    · simpa [one] using bit
    · apply fits_le small
      simp [one]
  have h4 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) (complement3 data) (complement4 data) 1 := by
    simpa using NaturalData.add_exec (complement3 data) Reg.address Reg.output Reg.index (by simpa using destination)
  have h5 : NaturalData.Exec w (.atom (.store Reg.address Reg.left)) (complement4 data) (complement5 data) 1 := by
    apply NaturalData.store_exec
    · simpa using destination
    · apply fits_le small
      simp [one]
  have h6 : NaturalData.Exec w (.atom (.arithmetic .add Reg.index Reg.index Reg.one)) (complement5 data) (complementStep data) 1 := by
    apply NaturalData.add_exec
    simpa [one] using indexFits
  simpa only [NaturalData.Exec,complementBody,complement1,Nat.reduceAdd] using
    h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))

structure ComplementLayout where
  input : ℕ
  output : ℕ
  length : ℕ
  disjoint : ∀ i< length, ∀ j< length, i< j → output+i≠input+j

structure ComplementRepresents (p : ComplementLayout) (source : ℕ → ℕ) (i : ℕ) (data : Data) : Prop where
  index : data.1 Reg.index=i
  length : data.1 Reg.length=p.length
  first : data.1 Reg.first=p.input
  output : data.1 Reg.output=p.output
  one : data.1 Reg.one=1
  input : ∀ j, i≤j → j< p.length → data.2 (p.input+j)=source (p.input+j)
  input_bits : ∀ j< p.length, source (p.input+j)≤1
  output_bits : ∀ j< i, data.2 (p.output+j)≤1
  frame : ∀ address, (address< p.output ∨ p.output+i≤address) → data.2 address=source address
  result : value data.2 p.output i+value source p.input i=2^i-1

theorem ComplementRepresents.step {p : ComplementLayout} {source : ℕ → ℕ} {i : ℕ} {data : Data}
    (h : ComplementRepresents p source i data) (within : i< p.length) :
    ComplementRepresents p source (i+1) (complementStep data) := by
  have regs := complementStep_registers data
  have mem := complementStep_memory data
  have sourceBit := h.input_bits i within
  have read : data.2 (data.1 Reg.first+data.1 Reg.index)=source (p.input+i) := by
    rw [h.first,h.index,h.input i (le_refl _) within]
  constructor
  · simp [regs,h.index,h.one]
  · simp [regs,h.length]
  · simp [regs,h.first]
  · simp [regs,h.output]
  · simp [regs,h.one]
  · intro j later hj
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by simpa using (p.disjoint i within j hj (by omega)).symm)]
    exact h.input j (by omega) hj
  · exact h.input_bits
  · intro j hj
    rw [mem,h.output,h.index]
    by_cases same : j=i
    · subst j
      simp only [Function.update_self]
      rw [h.one]
      omega
    · rw [Function.update_of_ne (by omega : p.output+j≠p.output+i)]
      exact h.output_bits j (by omega)
  · intro address outside
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by omega : address≠p.output+i)]
    exact h.frame address (by omega)
  · rw [mem,read,h.one,h.output,h.index,value_write,value_succ,pow_succ]
    have result := h.result
    have power : 1≤(2:ℕ)^i := Nat.one_le_two_pow
    have cancel : 1-source (p.input+i)+source (p.input+i)=1 := Nat.sub_add_cancel sourceBit
    have scaled := congrArg (fun n : ℕ => n*2^i) cancel
    have old : value data.2 p.output i+value source p.input i+1=2^i := by omega
    have larger : 1≤2^i*2 := by omega
    have recover := Nat.sub_add_cancel larger
    nlinarith only [old,scaled,recover]

def complementLoop : Code := .loop (.lt Reg.index Reg.length) complementBody

theorem complementLoop_exec {w : ℕ} (p : ComplementLayout) (source : ℕ → ℕ)
    (small : Fits w (1:ℕ))
    (inputFits : Fits w (p.input+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) (remaining : ℕ) :
    ∀ i data, p.length=i+remaining → ComplementRepresents p source i data →
    ∃ result, NaturalData.Exec w complementLoop data result (8*remaining+2) ∧
      ComplementRepresents p source p.length result := by
  induction remaining with
  | zero =>
    intro i data length h
    have equal : i=p.length := by omega
    subst i
    refine ⟨data,?_,h⟩
    apply Structured.Exec.loop_done
    simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length]
  | succ remaining ih =>
    intro i data length h
    have within : i< p.length := by omega
    have body := complementBody_exec data h.one
      (by rw [h.first,h.index,h.input i (le_refl _) within]; exact h.input_bits i within)
      small
      (by rw [h.first,h.index]; exact fits_le inputFits (by omega))
      (by rw [h.output,h.index]; exact fits_le outputFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,rest,correct⟩ := ih (i+1) (complementStep data) (by omega) (h.step within)
    refine ⟨result,?_,correct⟩
    have holds : (Structured.Condition.lt Reg.index Reg.length).Holds data.word := by
      simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length,within]
    have run := Structured.Exec.loop_more holds body rest
    convert run using 1 <;> (try simp only [complementLoop]) <;> omega

def complementInitialize : Code :=
  .seq (.atom (.constant Reg.index 0)) (.atom (.constant Reg.one 1))

def complementInitialized (data : Data) := (data.set Reg.index 0).set Reg.one 1

def complementProgram : Code := .seq complementInitialize complementLoop

theorem complementInitialize_exec {w : ℕ} (data : Data) (small : Fits w (1:ℕ)) :
    NaturalData.Exec w complementInitialize data (complementInitialized data) 2 := by
  exact (NaturalData.constant_exec data Reg.index 0 (fits_le small (by omega : 0≤1))).seq
    (NaturalData.constant_exec (data.set Reg.index 0) Reg.one 1 small)

theorem complementInitialized_represents (p : ComplementLayout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.input)
    (output : data.1 Reg.output=p.output)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1) :
    ComplementRepresents p data.2 0 (complementInitialized data) := by
  constructor <;> simp_all [complementInitialized]

/-- Complete bitwise complement, with checked addresses, unchanged external
memory, and the exact arithmetic interpretation of the resulting digits. -/
theorem complementProgram_exec {w : ℕ} (p : ComplementLayout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.input)
    (output : data.1 Reg.output=p.output)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1)
    (small : Fits w (1:ℕ))
    (inputFits : Fits w (p.input+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w complementProgram data result (8*p.length+4) ∧
      ComplementRepresents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := complementLoop_exec p data.2 small inputFits outputFits
    lengthFits p.length 0 (complementInitialized data) (by omega)
    (complementInitialized_represents p data length first output bits)
  refine ⟨result,?_,correct⟩
  have full := (complementInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [complementProgram]) <;> omega

end LeanTrominoes.Domino.WordRAM.Binary

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMComplement

/-! # Copying binary arrays with checked word addresses -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM
attribute [local simp] Reg.index Reg.length Reg.first Reg.output Reg.left Reg.one Reg.address
  NaturalData.set NaturalData.store

def copyBody : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) <|
  .seq (.atom (.store Reg.address Reg.left))
       (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def copy1 (data : Data) := data.set Reg.address (data.1 Reg.first+data.1 Reg.index)
def copy2 (data : Data) := (copy1 data).set Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index))
def copy3 (data : Data) := (copy2 data).set Reg.address (data.1 Reg.output+data.1 Reg.index)
def copy4 (data : Data) := (copy3 data).store ((copy3 data).1 Reg.address) ((copy3 data).1 Reg.left)
def copyStep (data : Data) := (copy4 data).set Reg.index ((copy4 data).1 Reg.index+(copy4 data).1 Reg.one)
attribute [local simp] copy1 copy2 copy3 copy4 copyStep

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem copyStep_registers (data : Data) :
    (copyStep data).1=Function.update
      (Function.update (Function.update data.1 Reg.left
        (data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.address (data.1 Reg.output+data.1 Reg.index))
        Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;> simp

theorem copyStep_memory (data : Data) :
    (copyStep data).2=Function.update data.2 (data.1 Reg.output+data.1 Reg.index)
      (data.2 (data.1 Reg.first+data.1 Reg.index)) := by simp

theorem copyBody_exec {w : ℕ} (data : Data) (one : data.1 Reg.one=1)
    (bit : data.2 (data.1 Reg.first+data.1 Reg.index)≤1)
    (small : Fits w (1:ℕ))
    (source : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (destination : Fits w (data.1 Reg.output+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    NaturalData.Exec w copyBody data (copyStep data) 5 := by
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index source
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (copy1 data) (copy2 data) 1 := by
    simpa using NaturalData.load_exec (copy1 data) Reg.left Reg.address
      (by simpa using source) (by simpa using fits_le small bit)
  have h3 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) (copy2 data) (copy3 data) 1 := by
    simpa using NaturalData.add_exec (copy2 data) Reg.address Reg.output Reg.index (by simpa using destination)
  have h4 : NaturalData.Exec w (.atom (.store Reg.address Reg.left)) (copy3 data) (copy4 data) 1 := by
    apply NaturalData.store_exec
    · simpa using destination
    · simpa using fits_le small bit
  have h5 : NaturalData.Exec w (.atom (.arithmetic .add Reg.index Reg.index Reg.one)) (copy4 data) (copyStep data) 1 := by
    apply NaturalData.add_exec
    simpa [one] using indexFits
  simpa only [NaturalData.Exec,copyBody,copy1,Nat.reduceAdd] using h1.seq (h2.seq (h3.seq (h4.seq h5)))

structure CopyRepresents (p : ComplementLayout) (source : ℕ → ℕ) (i : ℕ) (data : Data) : Prop where
  index : data.1 Reg.index=i
  length : data.1 Reg.length=p.length
  first : data.1 Reg.first=p.input
  output : data.1 Reg.output=p.output
  one : data.1 Reg.one=1
  input : ∀ j, i≤j → j< p.length → data.2 (p.input+j)=source (p.input+j)
  input_bits : ∀ j< p.length, source (p.input+j)≤1
  output_bits : ∀ j< i, data.2 (p.output+j)≤1
  frame : ∀ address, (address< p.output ∨ p.output+i≤address) → data.2 address=source address
  result : value data.2 p.output i=value source p.input i

theorem CopyRepresents.step {p : ComplementLayout} {source : ℕ → ℕ} {i : ℕ} {data : Data}
    (h : CopyRepresents p source i data) (within : i< p.length) :
    CopyRepresents p source (i+1) (copyStep data) := by
  have regs := copyStep_registers data
  have mem := copyStep_memory data
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
    rw [mem,read,h.output,h.index]
    by_cases same : j=i
    · subst j
      simpa using h.input_bits i within
    · rw [Function.update_of_ne (by omega : p.output+j≠p.output+i)]
      exact h.output_bits j (by omega)
  · intro address outside
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by omega : address≠p.output+i)]
    exact h.frame address (by omega)
  · rw [mem,read,h.output,h.index,value_write,value_succ,h.result]

def copyLoop : Code := .loop (.lt Reg.index Reg.length) copyBody

theorem copyLoop_exec {w : ℕ} (p : ComplementLayout) (source : ℕ → ℕ)
    (small : Fits w (1:ℕ))
    (inputFits : Fits w (p.input+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) (remaining : ℕ) :
    ∀ i data, p.length=i+remaining → CopyRepresents p source i data →
    ∃ result, NaturalData.Exec w copyLoop data result (7*remaining+2) ∧
      CopyRepresents p source p.length result := by
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
    have body := copyBody_exec data h.one
      (by rw [h.first,h.index,h.input i (le_refl _) within]; exact h.input_bits i within)
      small
      (by rw [h.first,h.index]; exact fits_le inputFits (by omega))
      (by rw [h.output,h.index]; exact fits_le outputFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,rest,correct⟩ := ih (i+1) (copyStep data) (by omega) (h.step within)
    refine ⟨result,?_,correct⟩
    have holds : (Structured.Condition.lt Reg.index Reg.length).Holds data.word := by
      simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length,within]
    have run := Structured.Exec.loop_more holds body rest
    convert run using 1 <;> (try simp only [copyLoop]) <;> omega


def copyProgram : Code := .seq complementInitialize copyLoop

theorem copyInitialized_represents (p : ComplementLayout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.input)
    (output : data.1 Reg.output=p.output)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1) :
    CopyRepresents p data.2 0 (complementInitialized data) := by
  constructor <;> simp_all [complementInitialized]

/-- Complete binary copy with exact primitive cost and external memory frame. -/
theorem copyProgram_exec {w : ℕ} (p : ComplementLayout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.input)
    (output : data.1 Reg.output=p.output)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1)
    (small : Fits w (1:ℕ))
    (inputFits : Fits w (p.input+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w copyProgram data result (7*p.length+4) ∧
      CopyRepresents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := copyLoop_exec p data.2 small inputFits outputFits
    lengthFits p.length 0 (complementInitialized data) (by omega)
    (copyInitialized_represents p data length first output bits)
  refine ⟨result,?_,correct⟩
  have full := (complementInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [copyProgram]) <;> omega

end LeanTrominoes.Domino.WordRAM.Binary

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition

/-! # In-place shift with a low input bit

The loop shifts a binary array one position toward the high end. It inserts
one input bit and returns the displaced high bit as carry, using only ordinary
loads, stores, register copies, and bounded address arithmetic.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM
attribute [local simp] Reg.index Reg.length Reg.first Reg.carry Reg.left Reg.one Reg.address
  NaturalData.set NaturalData.store

def shiftBody : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.store Reg.address Reg.carry)) <|
  .seq (.atom (.copy Reg.carry Reg.left))
       (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def shift1 (data : Data) := data.set Reg.address (data.1 Reg.first+data.1 Reg.index)
def shift2 (data : Data) := (shift1 data).set Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index))
def shift3 (data : Data) := (shift2 data).store ((shift2 data).1 Reg.address) ((shift2 data).1 Reg.carry)
def shift4 (data : Data) := (shift3 data).set Reg.carry ((shift3 data).1 Reg.left)
def shiftStep (data : Data) := (shift4 data).set Reg.index ((shift4 data).1 Reg.index+(shift4 data).1 Reg.one)

attribute [local simp] shift1 shift2 shift3 shift4 shiftStep

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem shiftStep_registers (data : Data) :
    (shiftStep data).1=Function.update
      (Function.update
        (Function.update (Function.update data.1 Reg.address (data.1 Reg.first+data.1 Reg.index))
          Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.carry (data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;> simp

theorem shiftStep_memory (data : Data) :
    (shiftStep data).2=Function.update data.2 (data.1 Reg.first+data.1 Reg.index) (data.1 Reg.carry) := by simp

theorem shiftBody_exec {w : ℕ} (data : Data) (one : data.1 Reg.one=1)
    (bit : data.2 (data.1 Reg.first+data.1 Reg.index)≤1) (carry : data.1 Reg.carry≤1)
    (small : Fits w (1:ℕ)) (address : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    NaturalData.Exec w shiftBody data (shiftStep data) 5 := by
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index address
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (shift1 data) (shift2 data) 1 := by
    simpa using NaturalData.load_exec (shift1 data) Reg.left Reg.address
      (by simpa using address) (by simpa using fits_le small bit)
  have h3 : NaturalData.Exec w (.atom (.store Reg.address Reg.carry)) (shift2 data) (shift3 data) 1 := by
    apply NaturalData.store_exec
    · simpa using address
    · simpa using fits_le small carry
  have h4 : NaturalData.Exec w (.atom (.copy Reg.carry Reg.left)) (shift3 data) (shift4 data) 1 := by
    apply NaturalData.copy_exec
    simpa using fits_le small bit
  have h5 : NaturalData.Exec w (.atom (.arithmetic .add Reg.index Reg.index Reg.one)) (shift4 data) (shiftStep data) 1 := by
    apply NaturalData.add_exec
    simpa [one] using indexFits
  simpa only [NaturalData.Exec,shiftBody,shift1,Nat.reduceAdd] using h1.seq (h2.seq (h3.seq (h4.seq h5)))

structure ShiftRepresents (base length low : ℕ) (source : ℕ → ℕ) (i : ℕ) (data : Data) : Prop where
  index : data.1 Reg.index=i
  length_eq : data.1 Reg.length=length
  first : data.1 Reg.first=base
  one : data.1 Reg.one=1
  carry : data.1 Reg.carry≤1
  input : ∀ j, i≤j → j< length → data.2 (base+j)=source (base+j)
  input_bits : ∀ j< length, source (base+j)≤1
  output_bits : ∀ j< i, data.2 (base+j)≤1
  frame : ∀ address, (address< base ∨ base+i≤address) → data.2 address=source address
  result : value data.2 base i+data.1 Reg.carry*2^i=2*value source base i+low

theorem ShiftRepresents.step {base length low i : ℕ} {source : ℕ → ℕ} {data : Data}
    (h : ShiftRepresents base length low source i data) (within : i< length) :
    ShiftRepresents base length low source (i+1) (shiftStep data) := by
  have regs := shiftStep_registers data
  have mem := shiftStep_memory data
  have read : data.2 (data.1 Reg.first+data.1 Reg.index)=source (base+i) := by
    rw [h.first,h.index,h.input i (le_refl _) within]
  constructor
  · simp [regs,h.index,h.one]
  · simp [regs,h.length_eq]
  · simp [regs,h.first]
  · simp [regs,h.one]
  · simp only [regs]
    simp [read,h.input_bits i within]
  · intro j later hj
    rw [mem,h.first,h.index]
    rw [Function.update_of_ne (by omega : base+j≠base+i)]
    exact h.input j (by omega) hj
  · exact h.input_bits
  · intro j hj
    rw [mem,h.first,h.index]
    by_cases same : j=i
    · subst j
      simpa using h.carry
    · rw [Function.update_of_ne (by omega : base+j≠base+i)]
      exact h.output_bits j (by omega)
  · intro address outside
    rw [mem,h.first,h.index]
    rw [Function.update_of_ne (by omega : address≠base+i)]
    exact h.frame address (by omega)
  · rw [mem,h.first,h.index,value_write,value_succ,pow_succ]
    have carryEq : (shiftStep data).1 Reg.carry=source (base+i) := by simp [regs,read]
    rw [carryEq]
    nlinarith only [h.result]

def shiftLoop : Code := .loop (.lt Reg.index Reg.length) shiftBody

theorem shiftLoop_exec {w : ℕ} (base length low : ℕ) (source : ℕ → ℕ)
    (small : Fits w (1:ℕ)) (addressFits : Fits w (base+length : ℕ))
    (lengthFits : Fits w length) (remaining : ℕ) :
    ∀ i data, length=i+remaining → ShiftRepresents base length low source i data →
    ∃ result, NaturalData.Exec w shiftLoop data result (7*remaining+2) ∧
      ShiftRepresents base length low source length result := by
  induction remaining with
  | zero =>
    intro i data lengthEq h
    have equal : i=length := by omega
    subst i
    refine ⟨data,?_,h⟩
    apply Structured.Exec.loop_done
    simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length_eq]
  | succ remaining ih =>
    intro i data lengthEq h
    have within : i< length := by omega
    have body := shiftBody_exec data h.one
      (by rw [h.first,h.index,h.input i (le_refl _) within]; exact h.input_bits i within)
      h.carry small
      (by rw [h.first,h.index]; exact fits_le addressFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,rest,correct⟩ := ih (i+1) (shiftStep data) (by omega) (h.step within)
    refine ⟨result,?_,correct⟩
    have holds : (Structured.Condition.lt Reg.index Reg.length).Holds data.word := by
      simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length_eq,within]
    have run := Structured.Exec.loop_more holds body rest
    convert run using 1 <;> (try simp only [shiftLoop]) <;> omega

def shiftInitialize : Code := .seq (.atom (.constant Reg.index 0)) (.atom (.constant Reg.one 1))
def shiftInitialized (data : Data) := (data.set Reg.index 0).set Reg.one 1
def shiftProgram : Code := .seq shiftInitialize shiftLoop

theorem shiftInitialize_exec {w : ℕ} (data : Data) (small : Fits w (1:ℕ)) :
    NaturalData.Exec w shiftInitialize data (shiftInitialized data) 2 := by
  exact (NaturalData.constant_exec data Reg.index 0 (fits_le small (by omega : 0≤1))).seq
    (NaturalData.constant_exec (data.set Reg.index 0) Reg.one 1 small)

theorem shiftInitialized_represents (base length : ℕ) (data : Data)
    (lengthEq : data.1 Reg.length=length) (first : data.1 Reg.first=base)
    (carry : data.1 Reg.carry≤1) (bits : ∀ j< length, data.2 (base+j)≤1) :
    ShiftRepresents base length (data.1 Reg.carry) data.2 0 (shiftInitialized data) := by
  constructor <;> simp_all [shiftInitialized]

/-- Complete exact instruction-count theorem for a binary left shift with an
arbitrary low input bit and a separate high output bit. -/
theorem shiftProgram_exec {w : ℕ} (base length : ℕ) (data : Data)
    (lengthEq : data.1 Reg.length=length) (first : data.1 Reg.first=base)
    (carry : data.1 Reg.carry≤1) (bits : ∀ j< length, data.2 (base+j)≤1)
    (small : Fits w (1:ℕ)) (addressFits : Fits w (base+length : ℕ))
    (lengthFits : Fits w length) :
    ∃ result, NaturalData.Exec w shiftProgram data result (7*length+4) ∧
      ShiftRepresents base length (data.1 Reg.carry) data.2 length result := by
  obtain ⟨result,run,correct⟩ := shiftLoop_exec base length (data.1 Reg.carry) data.2 small
    addressFits lengthFits length 0 (shiftInitialized data) (by omega)
    (shiftInitialized_represents base length data lengthEq first carry bits)
  refine ⟨result,?_,correct⟩
  have full := (shiftInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [shiftProgram]) <;> omega

end LeanTrominoes.Domino.WordRAM.Binary

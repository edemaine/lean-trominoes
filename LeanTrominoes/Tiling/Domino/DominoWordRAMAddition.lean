/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMBinary

/-! # Complete ripple-carry array addition

This routine has linear instruction count in the number of binary digits.
No arithmetic primitive operates on a multiword value.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

/-- A little-endian array prefix interpreted as a natural number. -/
def value (memory : ℕ → ℕ) (base length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, memory (base+i)*2^i

@[simp] theorem value_zero (memory : ℕ → ℕ) (base : ℕ) : value memory base 0=0 := by
  simp [value]

theorem value_succ (memory : ℕ → ℕ) (base length : ℕ) :
    value memory base (length+1)=value memory base length+memory (base+length)*2^length := by
  simp [value,Finset.sum_range_succ]

theorem value_congr {memory other : ℕ → ℕ} {base length : ℕ}
    (h : ∀ i< length, memory (base+i)=other (base+i)) : value memory base length=value other base length := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem value_write (memory : ℕ → ℕ) (base length digit : ℕ) :
    value (Function.update memory (base+length) digit) base (length+1)=
      value memory base length+digit*2^length := by
  rw [value_succ]
  simp only [Function.update_self]
  congr 1
  apply value_congr
  intro i hi
  rw [Function.update_of_ne (by omega : base+i≠base+length)]

/-- A write cannot overwrite a future input digit. Exact in-place addition
is allowed for either operand. -/
structure Layout where
  first : ℕ
  second : ℕ
  output : ℕ
  length : ℕ
  first_disjoint : ∀ i< length, ∀ j< length, i< j → output+i≠first+j
  second_disjoint : ∀ i< length, ∀ j< length, i< j → output+i≠second+j

/-- The ghost source memory records the original input digits, not computed
answers. The equality is the standard arithmetic invariant of addition. -/
structure Represents (p : Layout) (source : ℕ → ℕ) (i : ℕ) (data : Data) (bias : ℕ := 0) : Prop where
  index : data.1 Reg.index=i
  length : data.1 Reg.length=p.length
  first : data.1 Reg.first=p.first
  second : data.1 Reg.second=p.second
  output : data.1 Reg.output=p.output
  one : data.1 Reg.one=1
  two : data.1 Reg.two=2
  carry : data.1 Reg.carry≤1
  left : ∀ j, i≤ j → j< p.length → data.2 (p.first+j)=source (p.first+j)
  right : ∀ j, i≤ j → j< p.length → data.2 (p.second+j)=source (p.second+j)
  left_bits : ∀ j< p.length, source (p.first+j)≤1
  right_bits : ∀ j< p.length, source (p.second+j)≤1
  output_bits : ∀ j< i, data.2 (p.output+j)≤1
  frame : ∀ address, (address< p.output ∨ p.output+i≤ address) → data.2 address=source address
  result : value data.2 p.output i+data.1 Reg.carry*2^i=
    value source p.first i+value source p.second i+bias

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address

/-- A single physical iteration preserves the complete addition invariant. -/
theorem Represents.step {p : Layout} {source : ℕ → ℕ} {i bias : ℕ} {data : Data}
    (h : Represents p source i data bias) (within : i< p.length) :
    Represents p source (i+1) (addStep data) bias := by
  have regs := addStep_registers data
  have mem := addStep_memory data
  have sumBound : source (p.first+i)+source (p.second+i)+data.1 Reg.carry≤3 := by
    have := h.left_bits i within
    have := h.right_bits i within
    have := h.carry
    omega
  simp only [Reg.carry] at sumBound
  have sourceLeft := h.left i (le_refl _) within
  have sourceRight := h.right i (le_refl _) within
  have reads : data.2 (data.1 Reg.first+data.1 Reg.index)=source (p.first+i) ∧
      data.2 (data.1 Reg.second+data.1 Reg.index)=source (p.second+i) := by
    simp only [h.first,h.second,h.index]
    exact ⟨sourceLeft,sourceRight⟩
  constructor
  · simp [regs,h.index,h.one]
  · simp [regs,h.length]
  · simp [regs,h.first]
  · simp [regs,h.second]
  · simp [regs,h.output]
  · simp [regs,h.one]
  · simp [regs,h.two]
  · simp only [regs,Function.update_apply]
    norm_num
    rw [reads.1,reads.2,h.two]
    omega
  · intro j later hj
    rw [mem]
    rw [Function.update_of_ne (by simpa [h.output,h.index] using (p.first_disjoint i within j hj (by omega)).symm)]
    exact h.left j (by omega) hj
  · intro j later hj
    rw [mem]
    rw [Function.update_of_ne (by simpa [h.output,h.index] using (p.second_disjoint i within j hj (by omega)).symm)]
    exact h.right j (by omega) hj
  · exact h.left_bits
  · exact h.right_bits
  · intro j hj
    rw [mem,h.output,h.index]
    by_cases same : j=i
    · subst j
      simp only [Function.update_self]
      rw [h.two]
      omega
    · rw [Function.update_of_ne (by omega : p.output+j≠p.output+i)]
      exact h.output_bits j (by omega)
  · intro address outside
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by omega : address≠p.output+i)]
    exact h.frame address (by omega)
  · rw [mem,reads.1,reads.2,h.two,h.output,h.index,value_write]
    have carryEq : (addStep data).1 Reg.carry=
        (source (p.first+i)+source (p.second+i)+data.1 Reg.carry)/2 := by
      simp [regs,reads.1,reads.2,h.two]
    rw [carryEq,pow_succ,value_succ,value_succ]
    have division := Nat.mod_add_div (source (p.first+i)+source (p.second+i)+data.1 Reg.carry) 2
    have result := h.result
    have scaled := congrArg (fun n : ℕ => n*2^i) division
    nlinarith only [result,scaled]

def addLoop : Code := .loop (.lt Reg.index Reg.length) addBody

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤ bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

/-- The entire digit loop executes in exactly thirteen instructions per digit,
plus the two instructions of its final failed guard. -/
theorem addLoop_exec {w : ℕ} (p : Layout) (source : ℕ → ℕ)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) (remaining : ℕ) (bias : ℕ := 0) :
    ∀ i data, p.length=i+remaining → Represents p source i data bias →
    ∃ result, NaturalData.Exec w addLoop data result (13*remaining+2) ∧
      Represents p source p.length result bias := by
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
    have body := addBody_exec data h.one h.two h.carry
      (by rw [h.first,h.index,h.left i (le_refl _) within]; exact h.left_bits i within)
      (by rw [h.second,h.index,h.right i (le_refl _) within]; exact h.right_bits i within)
      small
      (by rw [h.first,h.index]; exact fits_le firstFits (by omega))
      (by rw [h.second,h.index]; exact fits_le secondFits (by omega))
      (by rw [h.output,h.index]; exact fits_le outputFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,rest,correct⟩ := ih (i+1) (addStep data) (by omega) (h.step within)
    refine ⟨result,?_,correct⟩
    have holds : (Structured.Condition.lt Reg.index Reg.length).Holds data.word := by
      simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length,within]
    have run := Structured.Exec.loop_more holds body rest
    convert run using 1 <;> (try simp only [addLoop]) <;> omega

def addInitialize : Code :=
  .seq (.atom (.constant Reg.index 0)) <|
  .seq (.atom (.constant Reg.carry 0)) <|
  .seq (.atom (.constant Reg.two 2)) (.atom (.constant Reg.one 1))

def addInitialized (data : Data) : Data :=
  (((data.set Reg.index 0).set Reg.carry 0).set Reg.two 2).set Reg.one 1

def addProgram : Code := .seq addInitialize addLoop

theorem addInitialize_exec {w : ℕ} (data : Data) (small : Fits w (3:ℕ)) :
    NaturalData.Exec w addInitialize data (addInitialized data) 4 := by
  have h0 := NaturalData.constant_exec data Reg.index 0 (fits_le small (by omega : 0≤3))
  have h1 := NaturalData.constant_exec (data.set Reg.index 0) Reg.carry 0 (fits_le small (by omega : 0≤3))
  have h2 := NaturalData.constant_exec ((data.set Reg.index 0).set Reg.carry 0) Reg.two 2 (fits_le small (by omega : 2≤3))
  have h3 := NaturalData.constant_exec (((data.set Reg.index 0).set Reg.carry 0).set Reg.two 2) Reg.one 1 (fits_le small (by omega : 1≤3))
  exact h0.seq (h1.seq (h2.seq h3))

theorem addInitialized_represents (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1) :
    Represents p data.2 0 (addInitialized data) := by
  constructor <;> simp_all [addInitialized,NaturalData.set]

/-- A complete actual RAM addition routine for arbitrary precision binary
arrays. The final carry is a separate bit. Precision is not constrained by the
word size: only the addresses, length, and the constants zero through three
must fit. -/
theorem addProgram_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w addProgram data result (13*p.length+6) ∧
      Represents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := addLoop_exec p data.2 small firstFits secondFits outputFits
    lengthFits p.length (bias:=0) 0 (addInitialized data) (by omega)
    (addInitialized_represents p data length first second output left right)
  refine ⟨result,?_,correct⟩
  have full := (addInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [addProgram]) <;> omega

/-- Carry-in one is used for two's-complement subtraction. -/
def addOneInitialize : Code :=
  .seq (.atom (.constant Reg.index 0)) <|
  .seq (.atom (.constant Reg.carry 1)) <|
  .seq (.atom (.constant Reg.two 2)) (.atom (.constant Reg.one 1))

def addOneInitialized (data : Data) : Data :=
  (((data.set Reg.index 0).set Reg.carry 1).set Reg.two 2).set Reg.one 1

def addOneProgram : Code := .seq addOneInitialize addLoop

theorem addOneInitialize_exec {w : ℕ} (data : Data) (small : Fits w (3:ℕ)) :
    NaturalData.Exec w addOneInitialize data (addOneInitialized data) 4 := by
  have h0 := NaturalData.constant_exec data Reg.index 0 (fits_le small (by omega : 0≤3))
  have h1 := NaturalData.constant_exec (data.set Reg.index 0) Reg.carry 1 (fits_le small (by omega : 1≤3))
  have h2 := NaturalData.constant_exec ((data.set Reg.index 0).set Reg.carry 1) Reg.two 2 (fits_le small (by omega : 2≤3))
  have h3 := NaturalData.constant_exec (((data.set Reg.index 0).set Reg.carry 1).set Reg.two 2) Reg.one 1 (fits_le small (by omega : 1≤3))
  exact h0.seq (h1.seq (h2.seq h3))

theorem addOneInitialized_represents (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1) :
    Represents p data.2 0 (addOneInitialized data) 1 := by
  constructor <;> simp_all [addOneInitialized,NaturalData.set]

/-- The same precision-independent routine with initial carry one. -/
theorem addOneProgram_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w addOneProgram data result (13*p.length+6) ∧
      Represents p data.2 p.length result 1 := by
  obtain ⟨result,run,correct⟩ := addLoop_exec p data.2 small firstFits secondFits outputFits
    lengthFits p.length (bias:=1) 0 (addOneInitialized data) (by omega)
    (addOneInitialized_represents p data length first second output left right)
  refine ⟨result,?_,correct⟩
  have full := (addOneInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [addOneProgram]) <;> omega

end LeanTrominoes.Domino.WordRAM.Binary

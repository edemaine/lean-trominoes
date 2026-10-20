/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMBorrow

/-! # Complete arbitrary-precision subtraction in bounded words -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

structure BorrowRepresents (p : Layout) (source : ℕ → ℕ) (i : ℕ) (data : Data) : Prop where
  index : data.1 Reg.index=i
  length : data.1 Reg.length=p.length
  first : data.1 Reg.first=p.first
  second : data.1 Reg.second=p.second
  output : data.1 Reg.output=p.output
  one : data.1 Reg.one=1
  two : data.1 Reg.two=2
  carry : data.1 Reg.carry≤1
  left : ∀ j, i≤j → j< p.length → data.2 (p.first+j)=source (p.first+j)
  right : ∀ j, i≤j → j< p.length → data.2 (p.second+j)=source (p.second+j)
  left_bits : ∀ j< p.length, source (p.first+j)≤1
  right_bits : ∀ j< p.length, source (p.second+j)≤1
  output_bits : ∀ j< i, data.2 (p.output+j)≤1
  frame : ∀ address, (address< p.output ∨ p.output+i≤address) → data.2 address=source address
  result : value data.2 p.output i+value source p.second i=
    value source p.first i+data.1 Reg.carry*2^i

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address

/-- Ripple borrow preserves exact subtraction, including the possible borrow
past the most significant digit. -/
theorem BorrowRepresents.step {p : Layout} {source : ℕ → ℕ} {i : ℕ} {data : Data}
    (h : BorrowRepresents p source i data) (within : i< p.length) :
    BorrowRepresents p source (i+1) (borrowStep data) := by
  have regs := borrowStep_registers data
  have mem := borrowStep_memory data
  have reads : data.2 (data.1 Reg.first+data.1 Reg.index)=source (p.first+i) ∧
      data.2 (data.1 Reg.second+data.1 Reg.index)=source (p.second+i) := by
    simp only [h.first,h.second,h.index]
    exact ⟨h.left i (le_refl _) within,h.right i (le_refl _) within⟩
  have leftBit := h.left_bits i within
  have rightBit := h.right_bits i within
  have carry := h.carry
  have term : borrowTerm data+source (p.second+i)+data.1 Reg.carry=source (p.first+i)+2 := by
    dsimp only [borrowTerm]
    rw [reads.1,reads.2,h.two]
    omega
  have bound : borrowTerm data≤3 := by omega
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
    rw [h.one,h.two]
    omega
  · intro j later hj
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by simpa using (p.first_disjoint i within j hj (by omega)).symm)]
    exact h.left j (by omega) hj
  · intro j later hj
    rw [mem,h.output,h.index]
    rw [Function.update_of_ne (by simpa using (p.second_disjoint i within j hj (by omega)).symm)]
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
  · rw [mem,h.two,h.output,h.index,value_write,value_succ,value_succ,pow_succ]
    have borrowEq : (borrowStep data).1 Reg.carry=1-borrowTerm data/2 := by simp [regs,h.one,h.two]
    rw [borrowEq]
    have division := Nat.mod_add_div (borrowTerm data) 2
    have localEq : borrowTerm data%2+source (p.second+i)+data.1 Reg.carry=
        source (p.first+i)+2*(1-borrowTerm data/2) := by omega
    have scaled := congrArg (fun n : ℕ => n*2^i) localEq
    nlinarith only [scaled,h.result]

def borrowLoop : Code := .loop (.lt Reg.index Reg.length) borrowBody

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem borrowLoop_exec {w : ℕ} (p : Layout) (source : ℕ → ℕ)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) (remaining : ℕ) :
    ∀ i data, p.length=i+remaining → BorrowRepresents p source i data →
    ∃ result, NaturalData.Exec w borrowLoop data result (15*remaining+2) ∧
      BorrowRepresents p source p.length result := by
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
    have body := borrowBody_exec data h.one h.two h.carry
      (by rw [h.first,h.index,h.left i (le_refl _) within]; exact h.left_bits i within)
      (by rw [h.second,h.index,h.right i (le_refl _) within]; exact h.right_bits i within)
      small
      (by rw [h.first,h.index]; exact fits_le firstFits (by omega))
      (by rw [h.second,h.index]; exact fits_le secondFits (by omega))
      (by rw [h.output,h.index]; exact fits_le outputFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,rest,correct⟩ := ih (i+1) (borrowStep data) (by omega) (h.step within)
    refine ⟨result,?_,correct⟩
    have holds : (Structured.Condition.lt Reg.index Reg.length).Holds data.word := by
      simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length,within]
    have run := Structured.Exec.loop_more holds body rest
    convert run using 1 <;> (try simp only [borrowLoop]) <;> omega

def borrowProgram : Code := .seq addInitialize borrowLoop

theorem borrowInitialized_represents (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1) :
    BorrowRepresents p data.2 0 (addInitialized data) := by
  constructor <;> simp_all [addInitialized,NaturalData.set]

/-- Full binary subtraction with a borrow bit, using at most three in digit
arithmetic. Operands may have arbitrarily many digits. -/
theorem borrowProgram_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first)
    (second : data.1 Reg.second=p.second) (output : data.1 Reg.output=p.output)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w borrowProgram data result (15*p.length+6) ∧
      BorrowRepresents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := borrowLoop_exec p data.2 small firstFits secondFits outputFits
    lengthFits p.length 0 (addInitialized data) (by omega)
    (borrowInitialized_represents p data length first second output left right)
  refine ⟨result,?_,correct⟩
  have full := (addInitialize_exec data small).seq run
  convert full using 1 <;> (try simp only [borrowProgram]) <;> omega

end LeanTrominoes.Domino.WordRAM.Binary

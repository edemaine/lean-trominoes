/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAbsoluteProgram
import LeanTrominoes.Tiling.Domino.DominoWordRAMValues

/-! # Correctness and exact cost of arbitrary-precision absolute value -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Absolute
open ComplexityAbstract.RAM

structure Layout where
  input : ℕ
  zero : ℕ
  output : ℕ
  length : ℕ
  input_safe : ∀ i< length, ∀ j< length, i< j → output+i≠input+j
  zero_safe : ∀ i< length, ∀ j< length, i< j → output+i≠zero+j

namespace Layout
def copyLayout (p : Layout) : ComplementLayout := ⟨p.input,p.output,p.length,p.input_safe⟩
def borrowLayout (p : Layout) : Binary.Layout :=
  ⟨p.zero,p.input,p.output,p.length,p.zero_safe,p.input_safe⟩
end Layout

structure Result (p : Layout) (source : ℕ → ℕ) (data : Data) : Prop where
  length : data.1 Reg.length=p.length
  output : data.1 Reg.output=p.output
  output_bits : ∀ j< p.length, data.2 (p.output+j)≤1
  frame : ∀ address, (address< p.output ∨ p.output+p.length≤address) → data.2 address=source address
  magnitude : value data.2 p.output p.length=
    if source (p.input+(p.length-1))=1 then 2^p.length-value source p.input p.length
    else value source p.input p.length

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address saved
  NaturalData.set header1 header2 header3 headed negate1 negate2 negatePrepared

theorem program_exec {w : ℕ} (p : Layout) (data : Data) (positive : 0< p.length)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.input)
    (second : data.1 Reg.second=p.zero) (output : data.1 Reg.output=p.output)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1)
    (zeros : ∀ j< p.length, data.2 (p.zero+j)=0)
    (small : Fits w (3:ℕ)) (inputFits : Fits w (p.input+p.length : ℕ))
    (zeroFits : Fits w (p.zero+p.length : ℕ)) (outputFits : Fits w (p.output+p.length : ℕ))
    (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧ cost≤15*p.length+14 ∧ Result p data.2 result := by
  have oneFits : Fits w (1:ℕ) := fits_le small (by omega)
  have lastBound := bits (p.length-1) (by omega)
  have headerRun := header_exec data (by rw [length]; exact positive) oneFits
    (by rw [length]; exact fits_le lengthFits (Nat.sub_le _ _))
    (by rw [first,length]; exact fits_le inputFits (by omega))
    (by rw [first,length]; exact fits_le oneFits lastBound)
  have headLeft : (headed data).1 Reg.left=data.2 (p.input+(p.length-1)) := by simp [first,length]
  have headOne : (headed data).1 Reg.one=1 := by simp
  have zeroValue : value data.2 p.zero p.length=0 := by
    unfold value
    apply Finset.sum_eq_zero
    intro j hj
    rw [zeros j (Finset.mem_range.mp hj),zero_mul]
  by_cases sign : data.2 (p.input+(p.length-1))=1
  · have condition : (Structured.Condition.eq Reg.left Reg.one).Holds (headed data).word := by
      change ((headed data).1 Reg.left : ℤ)=((headed data).1 Reg.one : ℤ)
      rw [headLeft,headOne,sign]
    have setupRun := negateSetup_exec (headed data)
      (by simpa [first] using fits_le inputFits (by omega : p.input≤p.input+p.length))
      (by simpa [second] using fits_le zeroFits (by omega : p.zero≤p.zero+p.length))
    obtain ⟨result,borrowRun,correct⟩ := borrowProgram_exec p.borrowLayout (negatePrepared (headed data))
      (by simp [length,Layout.borrowLayout]) (by simp [second,Layout.borrowLayout])
      (by simp [first,Layout.borrowLayout]) (by simp [output,Layout.borrowLayout])
      (fun j hj => by simp only [Layout.borrowLayout,NaturalData.set,negatePrepared,negate2,negate1,headed,header3,header2,header1]; rw [zeros j hj]; omega)
      bits small zeroFits inputFits outputFits lengthFits
    have branch := Structured.Exec.branch_yes (no := copyProgram) condition (setupRun.seq borrowRun)
    refine ⟨result,4+((3+(15*p.length+6))+1),?_,by omega,?_⟩
    · exact headerRun.seq branch
    · constructor
      · exact correct.length
      · exact correct.output
      · exact correct.output_bits
      · exact correct.frame
      · rw [if_pos sign]
        have equation := correct.result
        change value result.2 p.output p.length+value data.2 p.input p.length=
          value data.2 p.zero p.length+result.1 Reg.carry*2^p.length at equation
        rw [zeroValue,zero_add] at equation
        have valuePositive : 0< value data.2 p.input p.length := by
          have last := value_succ data.2 p.input (p.length-1)
          rw [show p.length-1+1=p.length by omega,sign,one_mul] at last
          have power : 1≤(2:ℕ)^(p.length-1) := Nat.one_le_two_pow
          omega
        have carryOne : result.1 Reg.carry=1 := by
          have bound := correct.carry
          by_contra different
          have zero : result.1 Reg.carry=0 := by omega
          rw [zero,zero_mul] at equation
          omega
        rw [carryOne,one_mul] at equation
        omega
  · have condition : ¬(Structured.Condition.eq Reg.left Reg.one).Holds (headed data).word := by
      simpa only [Structured.Condition.Holds,NaturalData.word,headLeft,headOne,Int.natCast_inj] using sign
    obtain ⟨result,copyRun,correct⟩ := copyProgram_exec p.copyLayout (headed data)
      (by simp [length,Layout.copyLayout]) (by simp [first,Layout.copyLayout]) (by simp [output,Layout.copyLayout])
      bits oneFits inputFits outputFits lengthFits
    have branch := Structured.Exec.branch_no (yes := negated) condition copyRun
    refine ⟨result,4+((7*p.length+4)+2),?_,by omega,?_⟩
    · exact headerRun.seq branch
    · constructor
      · exact correct.length
      · exact correct.output
      · exact correct.output_bits
      · exact correct.frame
      · rw [if_neg sign]
        exact correct.result

theorem program_size : program.size<128 := by decide

end LeanTrominoes.Domino.WordRAM.Binary.Absolute

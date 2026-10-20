/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderProgram

/-! # Checked calls made by the long-remainder loop -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM
attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address
  R.numerator R.denominator R.remainder R.difference R.precision R.count R.position R.address R.bit R.zero R.one
  low NaturalData.set

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem shifted_exec {w : ℕ} (data : WideData) (base length : ℕ)
    (pointer : data.1 R.remainder=base) (precision : data.1 R.precision=length)
    (bit : data.1 R.bit≤1) (bits : ∀ j< length, data.2 (base+j)≤1)
    (small : Fits w (1:ℕ)) (addressFits : Fits w (base+length : ℕ))
    (lengthFits : Fits w length) :
    ∃ result : Data, NaturalData.Exec w shifted data (extend result (upper data)) (7*length+7) ∧
      ShiftRepresents base length (data.1 R.bit) data.2 length result := by
  have preparedLength : (lower (shiftPrepared data)).1 Reg.length=length := by simp [lower,shiftPrepared,precision]
  have preparedFirst : (lower (shiftPrepared data)).1 Reg.first=base := by simp [lower,shiftPrepared,pointer]
  have preparedCarry : (lower (shiftPrepared data)).1 Reg.carry=data.1 R.bit := by simp [lower,shiftPrepared]
  obtain ⟨result,run,correct⟩ := shiftProgram_exec base length (lower (shiftPrepared data))
    preparedLength preparedFirst (by rw [preparedCarry]; exact bit) bits small addressFits lengthFits
  have call := call_exec run
  have upperEq : upper (shiftPrepared data)=upper data := by simp only [shiftPrepared,low,upper_set_lower]
  rw [upperEq] at call
  have setup := shiftSetup_exec data (by rw [pointer]; exact fits_le addressFits (by omega))
    (by rw [precision]; exact lengthFits) (fits_le small bit)
  refine ⟨result,?_,?_⟩
  · have full := setup.seq call
    convert full using 1 <;> (try simp only [shifted]) <;> omega
  · rw [preparedCarry] at correct
    exact correct

theorem subtracted_exec {w : ℕ} (p : Layout) (data : WideData)
    (first : data.1 R.remainder=p.first) (second : data.1 R.denominator=p.second)
    (output : data.1 R.difference=p.output) (precision : data.1 R.precision=p.length)
    (left : ∀ j< p.length, data.2 (p.first+j)≤1)
    (right : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (3:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result : Data, NaturalData.Exec w subtracted data (extend result (upper data)) (15*p.length+10) ∧
      BorrowRepresents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := borrowProgram_exec p (lower (borrowPrepared data))
    (by simp [lower,borrowPrepared,precision]) (by simp [lower,borrowPrepared,first])
    (by simp [lower,borrowPrepared,second]) (by simp [lower,borrowPrepared,output])
    left right small firstFits secondFits outputFits lengthFits
  have call := call_exec run
  have upperEq : upper (borrowPrepared data)=upper data := by simp only [borrowPrepared,low,upper_set_lower]
  rw [upperEq] at call
  have setup := borrowSetup_exec data
    (by rw [first]; exact fits_le firstFits (by omega))
    (by rw [second]; exact fits_le secondFits (by omega))
    (by rw [output]; exact fits_le outputFits (by omega))
    (by rw [precision]; exact lengthFits)
  refine ⟨result,?_,?_⟩
  · have full := setup.seq call
    convert full using 1 <;> (try simp only [subtracted]) <;> omega
  · exact correct

theorem accepted_exec {w : ℕ} (p : ComplementLayout) (data : WideData)
    (first : data.1 R.difference=p.input) (output : data.1 R.remainder=p.output)
    (precision : data.1 R.precision=p.length)
    (bits : ∀ j< p.length, data.2 (p.input+j)≤1)
    (small : Fits w (1:ℕ))
    (inputFits : Fits w (p.input+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result : Data, NaturalData.Exec w accepted data (extend result (upper data)) (7*p.length+7) ∧
      CopyRepresents p data.2 p.length result := by
  obtain ⟨result,run,correct⟩ := copyProgram_exec p (lower (copyPrepared data))
    (by simp [lower,copyPrepared,precision]) (by simp [lower,copyPrepared,first])
    (by simp [lower,copyPrepared,output]) bits small inputFits outputFits lengthFits
  have call := call_exec run
  have upperEq : upper (copyPrepared data)=upper data := by simp only [copyPrepared,low,upper_set_lower]
  rw [upperEq] at call
  have setup := copySetup_exec data
    (by rw [first]; exact fits_le inputFits (by omega))
    (by rw [output]; exact fits_le outputFits (by omega))
    (by rw [precision]; exact lengthFits)
  refine ⟨result,?_,?_⟩
  · have full := setup.seq call
    convert full using 1 <;> (try simp only [accepted]) <;> omega
  · exact correct

end LeanTrominoes.Domino.WordRAM.Binary.Remainder

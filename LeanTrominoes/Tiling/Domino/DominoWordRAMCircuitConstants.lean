/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitNodes

/-! # Physical zero and one nodes for binary arithmetic circuits -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

abbrev bitValue (bit : Bool) : ℕ := if bit then 1 else 0

def constantProgram (bit : Bool) (output : ℕ) : Code :=
  .seq (pointerProgram .output output) <|
  .seq (.atom (.constant (low Reg.left) (bitValue bit)))
       (.atom (.store (low Reg.output) (low Reg.left)))

def constantState (data : Data) (bit : Bool) (output : ℕ) : Data :=
  ((pointerState data .output output).set (low Reg.left) (bitValue bit)).store
    (slotBase (data.1 baseRegister) (data.1 (low Reg.length)) output) (bitValue bit)

/-- A single low-digit write in a zero array represents the selected constant. -/
theorem value_constant_write (memory : ℕ → ℕ) (base length digit : ℕ) (positive : 0< length)
    (zero : ∀ i< length, memory (base+i)=0) :
    Binary.value (Function.update memory base digit) base length=digit := by
  unfold Binary.value
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi different
    have ne : base+i≠base := by omega
    simp only [Function.update_of_ne ne,zero i (Finset.mem_range.mp hi),Nat.zero_mul]
  · intro missing
    have member : 0∈Finset.range length := Finset.mem_range.mpr positive
    exact False.elim (missing member)

structure ConstantResult (bit : Bool) (base length output : ℕ) (source : ℕ → ℕ) (data : Data) : Prop where
  base_eq : data.1 baseRegister=base
  length_eq : data.1 (low Reg.length)=length
  bits : ∀ i< length, data.2 (slotBase base length output+i)≤1
  frame : ∀ address, (address< slotBase base length output ∨ slotBase base length output+length≤address) →
    data.2 address=source address
  value : Binary.value data.2 (slotBase base length output) length=bitValue bit

/-- Five primitive instructions initialize one constant node. Unwritten digits
are the still-zero fresh array, and every external memory cell is preserved. -/
theorem constant_exec {w base length slots : ℕ} (bit : Bool) (data : Data) (output : ℕ)
    (baseEq : data.1 baseRegister=base) (lengthEq : data.1 (low Reg.length)=length)
    (positive : 0< length) (outputBound : output≤slots)
    (zero : ∀ i< length, data.2 (slotBase base length output+i)=0)
    (fits : Fits w (resourceBound base length slots)) :
    NaturalData.Exec w (constantProgram bit output) data (constantState data bit output) 5 ∧
      ConstantResult bit base length output data.2 (constantState data bit output) := by
  let p := pointerState data .output output
  let q := p.set (low Reg.left) (bitValue bit)
  have bitFits : Fits w (bitValue bit) := by
    apply Allocation.nat_fits_le fits
    cases bit <;> unfold resourceBound <;> simp only [bitValue,Bool.false_eq_true,ite_false,ite_true] <;> omega
  have r1 := pointer_exec_bounded data .output output baseEq lengthEq outputBound fits
  have r2 := NaturalData.constant_exec p (low Reg.left) (bitValue bit) bitFits
  have r3 : NaturalData.Exec w (.atom (.store (low Reg.output) (low Reg.left))) q
      (constantState data bit output) 1 := by
    have addressFits : Fits w (q.1 (low Reg.output)) := by
      simpa [q,p,pointerState,Pointer.register,NaturalData.set,baseEq,lengthEq,low,Reg.left,Reg.output]
        using Allocation.nat_fits_le (resource_end_fits fits outputBound) (by omega : base+output*length≤base+output*length+length)
    have valueFits : Fits w (q.1 (low Reg.left)) := by simpa [q,NaturalData.set] using bitFits
    have run := NaturalData.store_exec q (low Reg.output) (low Reg.left) addressFits valueFits
    simpa [q,p,constantState,pointerState,Pointer.register,NaturalData.set,low,Reg.left,Reg.output] using run
  refine ⟨r1.seq (r2.seq r3),?_⟩
  constructor
  · simpa [constantState,NaturalData.store,NaturalData.set,pointerState,Pointer.register,low,Reg.left,Reg.output,Reg.length,baseRegister] using baseEq
  · simpa [constantState,NaturalData.store,NaturalData.set,pointerState,Pointer.register,low,Reg.left,Reg.output,Reg.length,baseRegister] using lengthEq
  · intro i hi
    simp only [constantState,NaturalData.store,NaturalData.set,pointerState_memory,baseEq,lengthEq]
    by_cases same : i=0
    · subst i
      cases bit <;> simp [bitValue]
    · rw [Function.update_of_ne (by unfold slotBase; omega : slotBase base length output+i≠slotBase base length output),zero i hi]
      omega
  · intro address outside
    simp only [constantState,NaturalData.store,NaturalData.set,pointerState_memory,baseEq,lengthEq]
    rw [Function.update_of_ne (by omega : address≠slotBase base length output)]
  · simp only [constantState,NaturalData.store,NaturalData.set,pointerState_memory,baseEq,lengthEq]
    exact value_constant_write _ _ _ _ positive zero

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

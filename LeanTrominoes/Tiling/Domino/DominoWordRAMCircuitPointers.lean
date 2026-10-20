/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitArithmetic
import LeanTrominoes.Computation.RAM.NaturalArithmetic

/-! # Runtime pointers for fixed binary arithmetic circuits

A circuit uses equal-length arrays in consecutive slots. The length and base
are runtime words; only the slot numbers occur as constants in the program.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

abbrev Data := NaturalData 17
abbrev Code := Structured.Code 17
abbrev baseRegister : Fin 17 := 16
abbrev low (i : Fin 16) : Fin 17 := i.castAdd 1

inductive Pointer | first | second | output

def Pointer.register : Pointer → Fin 17
  | .first => low Reg.first
  | .second => low Reg.second
  | .output => low Reg.output

def pointerProgram (dst : Pointer) (slot : ℕ) : Code :=
  .seq (.atom (.constant (low Reg.left) slot)) <|
  .seq (.atom (.arithmetic .mul dst.register (low Reg.left) (low Reg.length)))
       (.atom (.arithmetic .add dst.register dst.register baseRegister))

def pointerState (data : Data) (dst : Pointer) (slot : ℕ) : Data :=
  ((data.set (low Reg.left) slot).set dst.register (slot*data.1 (low Reg.length))).set
    dst.register (data.1 baseRegister+slot*data.1 (low Reg.length))

attribute [local simp] low Reg.first Reg.second Reg.output Reg.left Reg.length baseRegister

/-- Three ordinary instructions compute base+slot*precision. -/
theorem pointer_exec {w : ℕ} (data : Data) (dst : Pointer) (slot : ℕ)
    (constantFits : Fits w slot) (productFits : Fits w (slot*data.1 (low Reg.length) : ℕ))
    (addressFits : Fits w (data.1 baseRegister+slot*data.1 (low Reg.length) : ℕ)) :
    NaturalData.Exec w (pointerProgram dst slot) data (pointerState data dst slot) 3 := by
  let a := data.set (low Reg.left) slot
  let b := a.set dst.register (slot*data.1 (low Reg.length))
  have r1 := NaturalData.constant_exec data (low Reg.left) slot constantFits
  have r2 : NaturalData.Exec w (.atom (.arithmetic .mul dst.register (low Reg.left) (low Reg.length))) a b 1 := by
    have fits : Fits w (a.1 (low Reg.left)*a.1 (low Reg.length) : ℕ) := by
      simpa [a,NaturalData.set] using productFits
    have run := NaturalData.mul_exec a dst.register (low Reg.left) (low Reg.length) fits
    simpa [a,b,NaturalData.set] using run
  have r3 : NaturalData.Exec w (.atom (.arithmetic .add dst.register dst.register baseRegister)) b
      (pointerState data dst slot) 1 := by
    have fits : Fits w (b.1 dst.register+b.1 baseRegister : ℕ) := by
      cases dst <;> simpa [b,a,Pointer.register,NaturalData.set,Nat.add_comm] using addressFits
    have run := NaturalData.add_exec b dst.register dst.register baseRegister fits
    cases dst <;> simpa [b,a,pointerState,Pointer.register,NaturalData.set,Nat.add_comm] using run
  exact r1.seq (r2.seq r3)

@[simp] theorem pointerState_base (data : Data) (dst : Pointer) (slot : ℕ) :
    (pointerState data dst slot).1 baseRegister=data.1 baseRegister := by
  cases dst <;> simp [pointerState,Pointer.register,NaturalData.set]

@[simp] theorem pointerState_length (data : Data) (dst : Pointer) (slot : ℕ) :
    (pointerState data dst slot).1 (low Reg.length)=data.1 (low Reg.length) := by
  cases dst <;> simp [pointerState,Pointer.register,NaturalData.set]

@[simp] theorem pointerState_memory (data : Data) (dst : Pointer) (slot : ℕ) :
    (pointerState data dst slot).2=data.2 := rfl

/-- Different slots have disjoint digit ranges, at every positive precision. -/
theorem slot_disjoint {base length first second i j : ℕ} (different : first≠second)
    (hi : i< length) (hj : j< length) :
    base+first*length+i≠base+second*length+j := by
  intro equal
  have positive : 0< length := by omega
  have withoutBase : length*first+i=length*second+j := by nlinarith only [equal]
  have quotients := congrArg (fun n : ℕ => n/length) withoutBase
  simp only [Nat.mul_add_div positive,Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hj,Nat.add_zero] at quotients
  exact different quotients

def resourceBound (base length slots : ℕ) : ℕ := base+(slots+1)*(length+1)+3

/-- One common bound covers coefficients, products, pointers, and array ends. -/
theorem resource_end_fits {w base length slots slot : ℕ}
    (fits : Fits w (resourceBound base length slots)) (within : slot≤slots) :
    Fits w (base+slot*length+length : ℕ) := by
  apply Allocation.nat_fits_le fits
  have product := Nat.mul_le_mul_right length within
  unfold resourceBound
  nlinarith

theorem pointer_exec_bounded {w base length slots : ℕ} (data : Data) (dst : Pointer) (slot : ℕ)
    (baseEq : data.1 baseRegister=base) (lengthEq : data.1 (low Reg.length)=length)
    (within : slot≤slots) (fits : Fits w (resourceBound base length slots)) :
    NaturalData.Exec w (pointerProgram dst slot) data (pointerState data dst slot) 3 := by
  have product := Nat.mul_le_mul_right length within
  apply pointer_exec
  · apply Allocation.nat_fits_le fits
    unfold resourceBound
    nlinarith
  · rw [lengthEq]
    apply Allocation.nat_fits_le fits
    unfold resourceBound
    nlinarith
  · rw [baseEq,lengthEq]
    exact Allocation.nat_fits_le (resource_end_fits fits within) (by omega)

def prepareProgram (first second output : ℕ) : Code :=
  .seq (pointerProgram .first first) (.seq (pointerProgram .second second) (pointerProgram .output output))

def prepared (data : Data) (first second output : ℕ) : Data :=
  pointerState (pointerState (pointerState data .first first) .second second) .output output

@[simp] theorem prepared_base (data : Data) (first second output : ℕ) :
    (prepared data first second output).1 baseRegister=data.1 baseRegister := by simp [prepared]

@[simp] theorem prepared_length (data : Data) (first second output : ℕ) :
    (prepared data first second output).1 (low Reg.length)=data.1 (low Reg.length) := by simp [prepared,pointerState,Pointer.register,NaturalData.set]

@[simp] theorem prepared_memory (data : Data) (first second output : ℕ) :
    (prepared data first second output).2=data.2 := rfl

@[simp] theorem prepared_first (data : Data) (first second output : ℕ) :
    (prepared data first second output).1 (low Reg.first)=
      data.1 baseRegister+first*data.1 (low Reg.length) := by
  simp [prepared,pointerState,Pointer.register,NaturalData.set]

@[simp] theorem prepared_second (data : Data) (first second output : ℕ) :
    (prepared data first second output).1 (low Reg.second)=
      data.1 baseRegister+second*data.1 (low Reg.length) := by
  simp [prepared,pointerState,Pointer.register,NaturalData.set]

@[simp] theorem prepared_output (data : Data) (first second output : ℕ) :
    (prepared data first second output).1 (low Reg.output)=
      data.1 baseRegister+output*data.1 (low Reg.length) := by
  simp [prepared,pointerState,Pointer.register,NaturalData.set]

theorem prepare_exec {w base length slots : ℕ} (data : Data) (first second output : ℕ)
    (baseEq : data.1 baseRegister=base) (lengthEq : data.1 (low Reg.length)=length)
    (firstBound : first≤slots) (secondBound : second≤slots) (outputBound : output≤slots)
    (fits : Fits w (resourceBound base length slots)) :
    NaturalData.Exec w (prepareProgram first second output) data (prepared data first second output) 9 := by
  have run1 := pointer_exec_bounded data .first first baseEq lengthEq firstBound fits
  have run2 := pointer_exec_bounded (pointerState data .first first) .second second
    (by simpa using baseEq) (by simpa [pointerState,Pointer.register,NaturalData.set] using lengthEq) secondBound fits
  have run3 := pointer_exec_bounded (pointerState (pointerState data .first first) .second second) .output output
    (by simpa using baseEq) (by simpa [pointerState,Pointer.register,NaturalData.set] using lengthEq) outputBound fits
  exact run1.seq (run2.seq run3)

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

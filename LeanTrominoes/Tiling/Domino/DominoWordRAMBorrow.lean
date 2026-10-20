/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition
import LeanTrominoes.Computation.RAM.NaturalArithmetic

/-! # Binary subtraction with a final borrow bit -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM
attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address
  NaturalData.set NaturalData.store add1 add2 add3 add4

def borrowBody : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) <|
  .seq (.atom (.load Reg.right Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.sum Reg.left Reg.two)) <|
  .seq (.atom (.arithmetic .sub Reg.sum Reg.sum Reg.right)) <|
  .seq (.atom (.arithmetic .sub Reg.sum Reg.sum Reg.carry)) <|
  .seq (.atom (.arithmetic .mod Reg.digit Reg.sum Reg.two)) <|
  .seq (.atom (.arithmetic .div Reg.carry Reg.sum Reg.two)) <|
  .seq (.atom (.arithmetic .sub Reg.carry Reg.one Reg.carry)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) <|
  .seq (.atom (.store Reg.address Reg.digit))
       (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def borrow5 (data : Data) := (add4 data).set Reg.sum ((add4 data).1 Reg.left+(add4 data).1 Reg.two)
def borrow6 (data : Data) := (borrow5 data).set Reg.sum ((borrow5 data).1 Reg.sum-(borrow5 data).1 Reg.right)
def borrow7 (data : Data) := (borrow6 data).set Reg.sum ((borrow6 data).1 Reg.sum-(borrow6 data).1 Reg.carry)
def borrow8 (data : Data) := (borrow7 data).set Reg.digit ((borrow7 data).1 Reg.sum%(borrow7 data).1 Reg.two)
def borrow9 (data : Data) := (borrow8 data).set Reg.carry ((borrow8 data).1 Reg.sum/(borrow8 data).1 Reg.two)
def borrow10 (data : Data) := (borrow9 data).set Reg.carry ((borrow9 data).1 Reg.one-(borrow9 data).1 Reg.carry)
def borrow11 (data : Data) := (borrow10 data).set Reg.address (data.1 Reg.output+data.1 Reg.index)
def borrow12 (data : Data) := (borrow11 data).store ((borrow11 data).1 Reg.address) ((borrow11 data).1 Reg.digit)
def borrowStep (data : Data) := (borrow12 data).set Reg.index ((borrow12 data).1 Reg.index+(borrow12 data).1 Reg.one)

def borrowTerm (data : Data) : ℕ := data.2 (data.1 Reg.first+data.1 Reg.index)+data.1 Reg.two-
  data.2 (data.1 Reg.second+data.1 Reg.index)-data.1 Reg.carry

attribute [local simp] borrow5 borrow6 borrow7 borrow8 borrow9 borrow10 borrow11 borrow12 borrowStep

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem borrowStep_registers (data : Data) :
    (borrowStep data).1=Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update data.1 Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.right (data.2 (data.1 Reg.second+data.1 Reg.index)))
        Reg.sum (borrowTerm data))
        Reg.digit (borrowTerm data%data.1 Reg.two))
        Reg.carry (data.1 Reg.one-borrowTerm data/data.1 Reg.two))
        Reg.address (data.1 Reg.output+data.1 Reg.index))
        Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;> simp [borrowTerm]

theorem borrowStep_memory (data : Data) :
    (borrowStep data).2=Function.update data.2 (data.1 Reg.output+data.1 Reg.index)
      (borrowTerm data%data.1 Reg.two) := by simp [borrowTerm]

/-- Every intermediate digit arithmetic value is at most three, independently
of the precision of the operands. -/
theorem borrowBody_exec {w : ℕ} (data : Data)
    (one : data.1 Reg.one=1) (two : data.1 Reg.two=2)
    (carry : data.1 Reg.carry≤1)
    (left : data.2 (data.1 Reg.first+data.1 Reg.index)≤1)
    (right : data.2 (data.1 Reg.second+data.1 Reg.index)≤1)
    (small : Fits w (3:ℕ))
    (firstAddress : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (secondAddress : Fits w (data.1 Reg.second+data.1 Reg.index : ℕ))
    (outputAddress : Fits w (data.1 Reg.output+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    NaturalData.Exec w borrowBody data (borrowStep data) 13 := by
  have smallFits (n : ℕ) (h : n≤3) : Fits w n := fits_le small h
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index firstAddress
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (add1 data) (add2 data) 1 := by
    simpa using NaturalData.load_exec (add1 data) Reg.left Reg.address
      (by simpa using firstAddress) (by simpa using smallFits _ (left.trans (by omega)))
  have h3 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) (add2 data) (add3 data) 1 := by
    simpa using NaturalData.add_exec (add2 data) Reg.address Reg.second Reg.index (by simpa using secondAddress)
  have h4 : NaturalData.Exec w (.atom (.load Reg.right Reg.address)) (add3 data) (add4 data) 1 := by
    simpa using NaturalData.load_exec (add3 data) Reg.right Reg.address
      (by simpa using secondAddress) (by simpa using smallFits _ (right.trans (by omega)))
  have h5 : NaturalData.Exec w (.atom (.arithmetic .add Reg.sum Reg.left Reg.two)) (add4 data) (borrow5 data) 1 := by
    apply NaturalData.add_exec
    apply smallFits
    simp [two]
    simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
  have h6 : NaturalData.Exec w (.atom (.arithmetic .sub Reg.sum Reg.sum Reg.right)) (borrow5 data) (borrow6 data) 1 := by
    apply NaturalData.sub_exec
    · simp [two]
      simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
    · apply smallFits
      simp [two]
      simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
  have h7 : NaturalData.Exec w (.atom (.arithmetic .sub Reg.sum Reg.sum Reg.carry)) (borrow6 data) (borrow7 data) 1 := by
    apply NaturalData.sub_exec
    · simp [two]
      simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
    · apply smallFits
      simp [two]
      simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
  have h8 : NaturalData.Exec w (.atom (.arithmetic .mod Reg.digit Reg.sum Reg.two)) (borrow7 data) (borrow8 data) 1 := by
    apply NaturalData.mod_exec
    apply smallFits
    simp [two]
    omega
  have h9 : NaturalData.Exec w (.atom (.arithmetic .div Reg.carry Reg.sum Reg.two)) (borrow8 data) (borrow9 data) 1 := by
    apply NaturalData.div_exec
    apply smallFits
    simp [two]
    simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
  have h10 : NaturalData.Exec w (.atom (.arithmetic .sub Reg.carry Reg.one Reg.carry)) (borrow9 data) (borrow10 data) 1 := by
    apply NaturalData.sub_exec
    · simp [one,two]
      simp_all only [Reg.first,Reg.second,Reg.index,Reg.carry] <;> omega
    · apply smallFits
      exact (Nat.sub_le _ _).trans (by simpa using (show (borrow9 data).1 Reg.one≤3 by simpa [one]))
  have h11 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) (borrow10 data) (borrow11 data) 1 := by
    simpa using NaturalData.add_exec (borrow10 data) Reg.address Reg.output Reg.index (by simpa using outputAddress)
  have h12 : NaturalData.Exec w (.atom (.store Reg.address Reg.digit)) (borrow11 data) (borrow12 data) 1 := by
    apply NaturalData.store_exec
    · simpa using outputAddress
    · apply smallFits
      simp [two]
      omega
  have h13 : NaturalData.Exec w (.atom (.arithmetic .add Reg.index Reg.index Reg.one)) (borrow12 data) (borrowStep data) 1 := by
    apply NaturalData.add_exec
    simpa [one] using indexFits
  simpa only [NaturalData.Exec,borrowBody,add1,Nat.reduceAdd] using
    h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq h13)))))))))))

end LeanTrominoes.Domino.WordRAM.Binary

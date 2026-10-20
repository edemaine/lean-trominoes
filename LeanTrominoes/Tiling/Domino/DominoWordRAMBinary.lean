/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalData

/-! # Binary multiword arithmetic in ordinary bounded-word instructions

Digits occupy separate words, least significant first. Arithmetic on digits
uses only values at most three. This supports integer inputs whose precision
exceeds one machine word; their bit length is charged as part of the input.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

abbrev Data := NaturalData 16
abbrev Code := Structured.Code 16
namespace Reg
abbrev index : Fin 16 := 0
abbrev length : Fin 16 := 1
abbrev first : Fin 16 := 2
abbrev second : Fin 16 := 3
abbrev output : Fin 16 := 4
abbrev carry : Fin 16 := 5
abbrev left : Fin 16 := 6
abbrev right : Fin 16 := 7
abbrev sum : Fin 16 := 8
abbrev digit : Fin 16 := 9
abbrev two : Fin 16 := 10
abbrev one : Fin 16 := 11
abbrev address : Fin 16 := 12
end Reg

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address

private theorem div_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left/data.1 right : ℕ)) :
    NaturalData.Exec w (.atom (.arithmetic .div dst left right)) data
      (data.set dst (data.1 left/data.1 right)) 1 := by
  rw [NaturalData.Exec,NaturalData.word_set]
  apply Structured.Exec.atom
  simpa [Structured.Primitive.eval,Arithmetic.eval,NaturalData.word] using fits

private theorem mod_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left%data.1 right : ℕ)) :
    NaturalData.Exec w (.atom (.arithmetic .mod dst left right)) data
      (data.set dst (data.1 left%data.1 right)) 1 := by
  rw [NaturalData.Exec,NaturalData.word_set]
  apply Structured.Exec.atom
  simpa [Structured.Primitive.eval,Arithmetic.eval,NaturalData.word] using fits

def addBody : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) <|
  .seq (.atom (.load Reg.right Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.sum Reg.left Reg.right)) <|
  .seq (.atom (.arithmetic .add Reg.sum Reg.sum Reg.carry)) <|
  .seq (.atom (.arithmetic .mod Reg.digit Reg.sum Reg.two)) <|
  .seq (.atom (.arithmetic .div Reg.carry Reg.sum Reg.two)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) <|
  .seq (.atom (.store Reg.address Reg.digit))
       (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def add1 (data : Data) := data.set Reg.address (data.1 Reg.first+data.1 Reg.index)
def add2 (data : Data) := (add1 data).set Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index))
def add3 (data : Data) := (add2 data).set Reg.address (data.1 Reg.second+data.1 Reg.index)
def add4 (data : Data) := (add3 data).set Reg.right (data.2 (data.1 Reg.second+data.1 Reg.index))
def add5 (data : Data) := (add4 data).set Reg.sum ((add4 data).1 Reg.left+(add4 data).1 Reg.right)
def add6 (data : Data) := (add5 data).set Reg.sum ((add5 data).1 Reg.sum+(add5 data).1 Reg.carry)
-- The next two definitions use the actual remainder and quotient instructions.
def addDigit (data : Data) := (add6 data).set Reg.digit ((add6 data).1 Reg.sum%(add6 data).1 Reg.two)
def addCarry (data : Data) := (addDigit data).set Reg.carry ((addDigit data).1 Reg.sum/(addDigit data).1 Reg.two)
def addAddress (data : Data) := (addCarry data).set Reg.address (data.1 Reg.output+data.1 Reg.index)
def addStore (data : Data) := (addAddress data).store ((addAddress data).1 Reg.address) ((addAddress data).1 Reg.digit)
def addStep (data : Data) := (addStore data).set Reg.index ((addStore data).1 Reg.index+(addStore data).1 Reg.one)

attribute [local simp] add1 add2 add3 add4 add5 add6 addDigit addCarry addAddress addStore addStep
  NaturalData.set NaturalData.store

/-- Exact scalar effect of one ripple-carry iteration. -/
theorem addStep_registers (data : Data) :
    (addStep data).1=Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update
      (Function.update data.1 Reg.left (data.2 (data.1 Reg.first+data.1 Reg.index)))
        Reg.right (data.2 (data.1 Reg.second+data.1 Reg.index)))
        Reg.sum (data.2 (data.1 Reg.first+data.1 Reg.index)+
          data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry))
        Reg.digit ((data.2 (data.1 Reg.first+data.1 Reg.index)+
          data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)%data.1 Reg.two))
        Reg.carry ((data.2 (data.1 Reg.first+data.1 Reg.index)+
          data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)/data.1 Reg.two))
        Reg.address (data.1 Reg.output+data.1 Reg.index))
        Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;> simp

theorem addStep_memory (data : Data) :
    (addStep data).2=Function.update data.2 (data.1 Reg.output+data.1 Reg.index)
      ((data.2 (data.1 Reg.first+data.1 Reg.index)+
        data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)%data.1 Reg.two) := by
  simp

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

/-- Eleven actual bounded-word instructions perform one binary full-adder.
Only addresses and the loop index depend on precision; arithmetic data stays
between zero and three. -/
theorem addBody_exec {w : ℕ} (data : Data)
    (one : data.1 Reg.one=1) (two : data.1 Reg.two=2)
    (carry : data.1 Reg.carry≤1)
    (left : data.2 (data.1 Reg.first+data.1 Reg.index)≤1)
    (right : data.2 (data.1 Reg.second+data.1 Reg.index)≤1)
    (small : Fits w (3:ℕ))
    (firstAddress : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (secondAddress : Fits w (data.1 Reg.second+data.1 Reg.index : ℕ))
    (outputAddress : Fits w (data.1 Reg.output+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    NaturalData.Exec w addBody data (addStep data) 11 := by
  have smallFits (n : ℕ) (h : n≤3) : Fits w n := fits_le small h
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index firstAddress
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (add1 data) (add2 data) 1 := by
    simpa using NaturalData.load_exec (add1 data) Reg.left Reg.address
      (by simpa using firstAddress) (by simpa using smallFits _ (by (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega) : data.2 (data.1 Reg.first+data.1 Reg.index)≤3))
  have h3 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) (add2 data) (add3 data) 1 := by
    simpa using NaturalData.add_exec (add2 data) Reg.address Reg.second Reg.index (by simpa using secondAddress)
  have h4 : NaturalData.Exec w (.atom (.load Reg.right Reg.address)) (add3 data) (add4 data) 1 := by
    simpa using NaturalData.load_exec (add3 data) Reg.right Reg.address
      (by simpa using secondAddress) (by simpa using smallFits _ (by (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega) : data.2 (data.1 Reg.second+data.1 Reg.index)≤3))
  have h5 : NaturalData.Exec w (.atom (.arithmetic .add Reg.sum Reg.left Reg.right)) (add4 data) (add5 data) 1 := by
    apply NaturalData.add_exec
    apply smallFits
    simp only [add4,add3,add2,add1,NaturalData.set] at *
    simp
    (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have h6 : NaturalData.Exec w (.atom (.arithmetic .add Reg.sum Reg.sum Reg.carry)) (add5 data) (add6 data) 1 := by
    apply NaturalData.add_exec
    apply smallFits
    simp
    (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have remainder : (data.2 (data.1 Reg.first+data.1 Reg.index)+data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)%2≤1 := by (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have quotient : (data.2 (data.1 Reg.first+data.1 Reg.index)+data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)/2≤1 := by (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have h7 : NaturalData.Exec w (.atom (.arithmetic .mod Reg.digit Reg.sum Reg.two)) (add6 data) (addDigit data) 1 := by
    apply mod_exec
    apply smallFits
    simp [two]
    (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have h8 : NaturalData.Exec w (.atom (.arithmetic .div Reg.carry Reg.sum Reg.two)) (addDigit data) (addCarry data) 1 := by
    apply div_exec
    apply smallFits
    simp [two]
    (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega)
  have h9 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.output Reg.index)) (addCarry data) (addAddress data) 1 := by
    simpa using NaturalData.add_exec (addCarry data) Reg.address Reg.output Reg.index (by simpa using outputAddress)
  have h10 : NaturalData.Exec w (.atom (.store Reg.address Reg.digit)) (addAddress data) (addStore data) 1 := by
    simpa [two] using NaturalData.store_exec (addAddress data) Reg.address Reg.digit
      (by simpa using outputAddress) (by simpa [two] using smallFits _ (by (simp_all only [Reg.one,Reg.two,Reg.carry,Reg.first,Reg.second,Reg.index]; omega) : (data.2 (data.1 Reg.first+data.1 Reg.index)+data.2 (data.1 Reg.second+data.1 Reg.index)+data.1 Reg.carry)%2≤3))
  have h11 : NaturalData.Exec w (.atom (.arithmetic .add Reg.index Reg.index Reg.one)) (addStore data) (addStep data) 1 := by
    simpa [one] using NaturalData.add_exec (addStore data) Reg.index Reg.index Reg.one (by simpa [one] using indexFits)
  simpa only [NaturalData.Exec,addBody,add1,Nat.reduceAdd] using
    h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq h11)))))))))

end LeanTrominoes.Domino.WordRAM.Binary

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRegisters
import LeanTrominoes.Tiling.Domino.DominoWordRAMShift
import LeanTrominoes.Tiling.Domino.DominoWordRAMSubtraction
import LeanTrominoes.Tiling.Domino.DominoWordRAMCopy
import LeanTrominoes.Tiling.Domino.DominoWordRAMValues

/-! # Binary long-remainder program

Each high-to-low numerator bit shifts the current remainder, subtracts the
denominator into a scratch array, and accepts that difference exactly when
there is no borrow. Every multiword operation is one of the checked digit
loops; no integer-valued mathematical function is used as an instruction.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

namespace R
abbrev numerator : Fin 32 := 16
abbrev denominator : Fin 32 := 17
abbrev remainder : Fin 32 := 18
abbrev difference : Fin 32 := 19
abbrev precision : Fin 32 := 20
abbrev count : Fin 32 := 21
abbrev position : Fin 32 := 22
abbrev address : Fin 32 := 23
abbrev bit : Fin 32 := 24
abbrev zero : Fin 32 := 25
abbrev one : Fin 32 := 26
end R

abbrev low (i : Fin 16) : Fin 32 := i.castAdd 16

def shiftSetup : WideCode :=
  .seq (.atom (.copy (low Reg.first) R.remainder)) <|
  .seq (.atom (.copy (low Reg.length) R.precision))
       (.atom (.copy (low Reg.carry) R.bit))

def borrowSetup : WideCode :=
  .seq (.atom (.copy (low Reg.first) R.remainder)) <|
  .seq (.atom (.copy (low Reg.second) R.denominator)) <|
  .seq (.atom (.copy (low Reg.output) R.difference))
       (.atom (.copy (low Reg.length) R.precision))

def copySetup : WideCode :=
  .seq (.atom (.copy (low Reg.first) R.difference)) <|
  .seq (.atom (.copy (low Reg.output) R.remainder))
       (.atom (.copy (low Reg.length) R.precision))

def shifted : WideCode := .seq shiftSetup (shiftProgram.embed 16)
def subtracted : WideCode := .seq borrowSetup (borrowProgram.embed 16)
def accepted : WideCode := .seq copySetup (copyProgram.embed 16)
def accept : WideCode := .branch (.eq (low Reg.carry) R.zero) accepted (.atom (.copy R.zero R.zero))

def readBit : WideCode :=
  .seq (.atom (.arithmetic .sub R.position R.position R.one)) <|
  .seq (.atom (.arithmetic .add R.address R.numerator R.position))
       (.atom (.load R.bit R.address))

def body : WideCode := .seq readBit (.seq shifted (.seq subtracted accept))
def loop : WideCode := .loop (.lt R.zero R.position) body

def initCode : WideCode :=
  .seq (.atom (.copy R.position R.count)) <|
  .seq (.atom (.constant R.zero 0)) (.atom (.constant R.one 1))

def program : WideCode := .seq initCode loop

def shiftPrepared (data : WideData) : WideData :=
  ((data.set (low Reg.first) (data.1 R.remainder)).set (low Reg.length) (data.1 R.precision)).set
    (low Reg.carry) (data.1 R.bit)

def borrowPrepared (data : WideData) : WideData :=
  (((data.set (low Reg.first) (data.1 R.remainder)).set (low Reg.second) (data.1 R.denominator)).set
    (low Reg.output) (data.1 R.difference)).set (low Reg.length) (data.1 R.precision)

def copyPrepared (data : WideData) : WideData :=
  ((data.set (low Reg.first) (data.1 R.difference)).set (low Reg.output) (data.1 R.remainder)).set
    (low Reg.length) (data.1 R.precision)

attribute [local simp] Reg.first Reg.second Reg.output Reg.carry Reg.length
  R.numerator R.denominator R.remainder R.difference R.precision R.count R.position R.address R.bit R.zero R.one
  low NaturalData.set

theorem shiftSetup_exec {w : ℕ} (data : WideData)
    (pointer : Fits w (data.1 R.remainder)) (precision : Fits w (data.1 R.precision))
    (bit : Fits w (data.1 R.bit)) :
    NaturalData.Exec w shiftSetup data (shiftPrepared data) 3 := by
  have h1 := NaturalData.copy_exec data (low Reg.first) R.remainder pointer
  have h2 := NaturalData.copy_exec (data.set (low Reg.first) (data.1 R.remainder)) (low Reg.length) R.precision (by simpa using precision)
  have h3 := NaturalData.copy_exec ((data.set (low Reg.first) (data.1 R.remainder)).set (low Reg.length) (data.1 R.precision)) (low Reg.carry) R.bit (by simpa using bit)
  exact h1.seq (h2.seq h3)

theorem borrowSetup_exec {w : ℕ} (data : WideData)
    (first : Fits w (data.1 R.remainder)) (second : Fits w (data.1 R.denominator))
    (output : Fits w (data.1 R.difference)) (precision : Fits w (data.1 R.precision)) :
    NaturalData.Exec w borrowSetup data (borrowPrepared data) 4 := by
  have h1 := NaturalData.copy_exec data (low Reg.first) R.remainder first
  have h2 := NaturalData.copy_exec (data.set (low Reg.first) (data.1 R.remainder)) (low Reg.second) R.denominator (by simpa using second)
  have h3 := NaturalData.copy_exec ((data.set (low Reg.first) (data.1 R.remainder)).set (low Reg.second) (data.1 R.denominator)) (low Reg.output) R.difference (by simpa using output)
  have h4 := NaturalData.copy_exec (((data.set (low Reg.first) (data.1 R.remainder)).set (low Reg.second) (data.1 R.denominator)).set (low Reg.output) (data.1 R.difference)) (low Reg.length) R.precision (by simpa using precision)
  exact h1.seq (h2.seq (h3.seq h4))

theorem copySetup_exec {w : ℕ} (data : WideData)
    (first : Fits w (data.1 R.difference)) (output : Fits w (data.1 R.remainder))
    (precision : Fits w (data.1 R.precision)) :
    NaturalData.Exec w copySetup data (copyPrepared data) 3 := by
  have h1 := NaturalData.copy_exec data (low Reg.first) R.difference first
  have h2 := NaturalData.copy_exec (data.set (low Reg.first) (data.1 R.difference)) (low Reg.output) R.remainder (by simpa using output)
  have h3 := NaturalData.copy_exec ((data.set (low Reg.first) (data.1 R.difference)).set (low Reg.output) (data.1 R.remainder)) (low Reg.length) R.precision (by simpa using precision)
  exact h1.seq (h2.seq h3)

end LeanTrominoes.Domino.WordRAM.Binary.Remainder

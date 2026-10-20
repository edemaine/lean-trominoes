/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSubtraction
import LeanTrominoes.Tiling.Domino.DominoWordRAMCopy

/-! # Absolute value of a binary two's-complement array

The high-bit test selects a direct copy or subtraction from an all-zero
array. The program operates on individual digit words at every precision.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Absolute
open ComplexityAbstract.RAM

abbrev saved : Fin 16 := 13

def header : Code :=
  .seq (.atom (.constant Reg.one 1)) <|
  .seq (.atom (.arithmetic .sub Reg.index Reg.length Reg.one)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index))
       (.atom (.load Reg.left Reg.address))

def negateSetup : Code :=
  .seq (.atom (.copy saved Reg.first)) <|
  .seq (.atom (.copy Reg.first Reg.second)) (.atom (.copy Reg.second saved))

def negated : Code := .seq negateSetup borrowProgram

def choose : Code := .branch (.eq Reg.left Reg.one) negated copyProgram

def program : Code := .seq header choose

def header1 (data : Data) := data.set Reg.one 1
def header2 (data : Data) := (header1 data).set Reg.index ((header1 data).1 Reg.length-(header1 data).1 Reg.one)
def header3 (data : Data) := (header2 data).set Reg.address ((header2 data).1 Reg.first+(header2 data).1 Reg.index)
def headed (data : Data) := (header3 data).set Reg.left ((header3 data).2 ((header3 data).1 Reg.address))

def negate1 (data : Data) := data.set saved (data.1 Reg.first)
def negate2 (data : Data) := (negate1 data).set Reg.first ((negate1 data).1 Reg.second)
def negatePrepared (data : Data) := (negate2 data).set Reg.second ((negate2 data).1 saved)

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output
  Reg.carry Reg.left Reg.right Reg.sum Reg.digit Reg.two Reg.one Reg.address saved
  NaturalData.set header1 header2 header3 headed negate1 negate2 negatePrepared

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem header_exec {w : ℕ} (data : Data) (positive : 0< data.1 Reg.length)
    (small : Fits w (1:ℕ)) (indexFits : Fits w (data.1 Reg.length-1 : ℕ))
    (addressFits : Fits w (data.1 Reg.first+(data.1 Reg.length-1) : ℕ))
    (bitFits : Fits w (data.2 (data.1 Reg.first+(data.1 Reg.length-1)))) :
    NaturalData.Exec w header data (headed data) 4 := by
  have h1 := NaturalData.constant_exec data Reg.one 1 small
  have h2 : NaturalData.Exec w (.atom (.arithmetic .sub Reg.index Reg.length Reg.one)) (header1 data) (header2 data) 1 := by
    apply NaturalData.sub_exec
    · simp
      exact positive
    · simpa using indexFits
  have h3 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) (header2 data) (header3 data) 1 := by
    apply NaturalData.add_exec
    simpa using addressFits
  have h4 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (header3 data) (headed data) 1 := by
    apply NaturalData.load_exec
    · simpa using addressFits
    · simpa using bitFits
  exact h1.seq (h2.seq (h3.seq h4))

theorem negateSetup_exec {w : ℕ} (data : Data)
    (first : Fits w (data.1 Reg.first)) (second : Fits w (data.1 Reg.second)) :
    NaturalData.Exec w negateSetup data (negatePrepared data) 3 := by
  have h1 := NaturalData.copy_exec data saved Reg.first first
  have h2 := NaturalData.copy_exec (negate1 data) Reg.first Reg.second (by simpa using second)
  have h3 := NaturalData.copy_exec (negate2 data) Reg.second saved (by simpa using first)
  exact h1.seq (h2.seq h3)

end LeanTrominoes.Domino.WordRAM.Binary.Absolute

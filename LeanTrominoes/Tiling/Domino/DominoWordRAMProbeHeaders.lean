/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMHeaderPointer

/-! # Installing one fresh decoder workspace's pointer headers -/
namespace LeanTrominoes.Domino.WordRAM.Binary.ProbeHeaders
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
abbrev low (i : Fin 64) : Fin 128 := i.castAdd 64
abbrev zero : Fin 128 := 75
abbrev determinant : Fin 128 := 76
abbrev twice : Fin 128 := 77
abbrev firstOrigin : Fin 128 := 78
abbrev secondOrigin : Fin 128 := 79

def moves : List (Fin 128 × Fin 128) :=
  [(low Numerator.G.precision,Reserve.precision),(low Numerator.G.zero,zero),
   (low Numerator.G.determinant,determinant),(low Numerator.G.twice,twice),
   (low SourceBlocks.firstOrigin,firstOrigin),(low SourceBlocks.secondOrigin,secondOrigin),
   (low SourceBlocks.precision,Reserve.precision),(low SourceBlocks.circuitBase,Reserve.base)]
def setup : Code := .seq (Assignments.code (low (BlockCopy.low Reg.length)) Reserve.precision moves)
  (.atom (.constant (low SourceBlocks.basisBase) 4))
def prepared (data : Data) : Data :=
  (Assignments.state (low (BlockCopy.low Reg.length)) Reserve.precision moves data).set (low SourceBlocks.basisBase) 4

def program (outputSlot workSlots : ℕ) : Code :=
  .seq setup <|
  .seq (HeaderPointer.program (low Numerator.G.numerator) outputSlot) <|
  .seq (HeaderPointer.program (low Numerator.G.absolute) workSlots) <|
  .seq (HeaderPointer.program (low Numerator.G.remainder) (workSlots+1))
       (HeaderPointer.program (low Numerator.G.difference) (workSlots+2))
def state (data : Data) (outputSlot workSlots : ℕ) : Data :=
  HeaderPointer.state (HeaderPointer.state (HeaderPointer.state
    (HeaderPointer.state (prepared data) (low Numerator.G.numerator) outputSlot)
      (low Numerator.G.absolute) workSlots) (low Numerator.G.remainder) (workSlots+1))
    (low Numerator.G.difference) (workSlots+2)

attribute [local simp] low Numerator.G.precision Numerator.G.numerator Numerator.G.zero Numerator.G.determinant
  Numerator.G.twice Numerator.G.absolute Numerator.G.remainder Numerator.G.difference SourceBlocks.firstOrigin
  SourceBlocks.secondOrigin SourceBlocks.precision SourceBlocks.circuitBase SourceBlocks.basisBase
  BlockCopy.low Reg.length Reserve.precision Reserve.base Reserve.factorRegister zero determinant twice firstOrigin secondOrigin
  NaturalData.set

theorem setup_exec {w : ℕ} (data : Data)
    (values : ∀ pair∈moves, Fits w (data.1 pair.2)) (four : Fits w (4:ℕ)) :
    NaturalData.Exec w setup data (prepared data) 10 := by
  have copies := Assignments.exec data (low (BlockCopy.low Reg.length)) Reserve.precision moves
    (values (low Numerator.G.precision,Reserve.precision) (by simp [moves])) values (by simp [moves]) (by simp [moves])
  have constant := NaturalData.constant_exec (Assignments.state (low (BlockCopy.low Reg.length)) Reserve.precision moves data)
    (low SourceBlocks.basisBase) 4 four
  exact copies.seq constant

theorem program_exec {w : ℕ} (data : Data) (outputSlot workSlots : ℕ)
    (values : ∀ pair∈moves, Fits w (data.1 pair.2)) (four : Fits w (4:ℕ))
    (slots : ∀ slot∈[outputSlot,workSlots,workSlots+1,workSlots+2], Fits w slot)
    (products : ∀ slot∈[outputSlot,workSlots,workSlots+1,workSlots+2], Fits w (slot*data.1 Reserve.precision : ℕ))
    (addresses : ∀ slot∈[outputSlot,workSlots,workSlots+1,workSlots+2], Fits w (data.1 Reserve.base+slot*data.1 Reserve.precision : ℕ)) :
    NaturalData.Exec w (program outputSlot workSlots) data (state data outputSlot workSlots) 22 := by
  have a := setup_exec data values four
  have b := HeaderPointer.program_exec (prepared data) (low Numerator.G.numerator) outputSlot (by decide) (by decide)
    (slots _ (by simp)) (by simpa [prepared,Assignments.state,moves] using products outputSlot (by simp))
    (by simpa [prepared,Assignments.state,moves] using addresses outputSlot (by simp))
  have c := HeaderPointer.program_exec (HeaderPointer.state (prepared data) (low Numerator.G.numerator) outputSlot)
    (low Numerator.G.absolute) workSlots (by decide) (by decide) (slots _ (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using products workSlots (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using addresses workSlots (by simp))
  have d := HeaderPointer.program_exec (HeaderPointer.state (HeaderPointer.state (prepared data) (low Numerator.G.numerator) outputSlot)
    (low Numerator.G.absolute) workSlots) (low Numerator.G.remainder) (workSlots+1) (by decide) (by decide) (slots _ (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using products (workSlots+1) (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using addresses (workSlots+1) (by simp))
  have e := HeaderPointer.program_exec (HeaderPointer.state (HeaderPointer.state (HeaderPointer.state (prepared data) (low Numerator.G.numerator) outputSlot)
    (low Numerator.G.absolute) workSlots) (low Numerator.G.remainder) (workSlots+1))
    (low Numerator.G.difference) (workSlots+2) (by decide) (by decide) (slots _ (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using products (workSlots+2) (by simp))
    (by simpa [HeaderPointer.state,prepared,Assignments.state,moves] using addresses (workSlots+2) (by simp))
  exact a.seq (b.seq (c.seq (d.seq e)))

theorem state_memory (data : Data) (outputSlot workSlots : ℕ) :
    (state data outputSlot workSlots).2=data.2 := rfl

theorem state_high (data : Data) (outputSlot workSlots : ℕ) (i : Fin 128) (high : 64≤ i.val) :
    (state data outputSlot workSlots).1 i=data.1 i := by
  have ne (j : Fin 64) : i≠low j := by intro eq; have val := congrArg Fin.val eq; have := j.isLt; simp only [low,Fin.val_castAdd] at val; omega
  have scratch : i≠Reserve.factorRegister := by intro eq; have val := congrArg Fin.val eq; change i.val=6 at val; omega
  simp only [state,HeaderPointer.state,NaturalData.set,Function.update_of_ne (ne Numerator.G.difference),
    Function.update_of_ne (ne Numerator.G.remainder),Function.update_of_ne (ne Numerator.G.absolute),
    Function.update_of_ne (ne Numerator.G.numerator),Function.update_of_ne scratch,prepared,
    Assignments.state,moves,List.foldl_cons,List.foldl_nil]
  simp only [NaturalData.set,Function.update_of_ne (ne SourceBlocks.basisBase),
    Function.update_of_ne (ne (BlockCopy.low Reg.length)),Function.update_of_ne (ne SourceBlocks.circuitBase),
    Function.update_of_ne (ne SourceBlocks.precision),Function.update_of_ne (ne SourceBlocks.secondOrigin),
    Function.update_of_ne (ne SourceBlocks.firstOrigin),Function.update_of_ne (ne Numerator.G.twice),
    Function.update_of_ne (ne Numerator.G.determinant),Function.update_of_ne (ne Numerator.G.zero),
    Function.update_of_ne (ne Numerator.G.precision)]

theorem numerator_controls (data : Data) (outputSlot workSlots : ℕ) (g : Numerator.Geometry)
    (precision_eq : g.precision=data.1 Reserve.precision)
    (numerator_eq : g.numerator=data.1 Reserve.base+outputSlot*data.1 Reserve.precision)
    (zero_eq : g.zero=data.1 zero) (determinant_eq : g.determinant=data.1 determinant)
    (twice_eq : g.twice=data.1 twice)
    (absolute_eq : g.absolute=data.1 Reserve.base+workSlots*data.1 Reserve.precision)
    (remainder_eq : g.remainder=data.1 Reserve.base+(workSlots+1)*data.1 Reserve.precision)
    (difference_eq : g.difference=data.1 Reserve.base+(workSlots+2)*data.1 Reserve.precision) :
    Numerator.Controls g (NaturalData.lower (r:=64) (s:=64) (state data outputSlot workSlots)) := by
  constructor <;> simp [state,HeaderPointer.state,prepared,Assignments.state,moves,NaturalData.lower,
    precision_eq,numerator_eq,zero_eq,determinant_eq,twice_eq,absolute_eq,remainder_eq,difference_eq]

theorem source_controls {n d : ℕ} (B : BasisData n d) (u v : Fin n) (data : Data) (outputSlot workSlots base : ℕ)
    (precision_eq : data.1 Reserve.precision=WordRAM.precision B) (base_eq : data.1 Reserve.base=base)
    (first_eq : data.1 firstOrigin=(sourceLayout B u v base).source 1)
    (second_eq : data.1 secondOrigin=(sourceLayout B u v base).source 2) :
    SourceLoad.Controls (sourceLayout B u v base)
      (NaturalData.lower (r:=64) (s:=64) (state data outputSlot workSlots)) := by
  constructor
  · simp [state,HeaderPointer.state,prepared,Assignments.state,moves,NaturalData.lower,sourceLayout,precision_eq]
  · simp [state,HeaderPointer.state,prepared,Assignments.state,moves,NaturalData.lower,sourceLayout,base_eq]
  · intro block
    fin_cases block <;> norm_num [SourceLoad.header,state,HeaderPointer.state,prepared,Assignments.state,moves,
      NaturalData.lower,sourceLayout,sourceRank,first_eq,second_eq,Fin.castAdd,Fin.castLE]

end LeanTrominoes.Domino.WordRAM.Binary.ProbeHeaders

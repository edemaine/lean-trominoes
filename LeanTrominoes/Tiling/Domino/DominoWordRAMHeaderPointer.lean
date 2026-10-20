/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMReserve

/-! # Runtime block addresses for the fixed decoder layout -/
namespace LeanTrominoes.Domino.WordRAM.Binary.HeaderPointer
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128

def program (destination : Fin 128) (slot : ℕ) : Code :=
  .seq (.atom (.constant Reserve.factorRegister slot)) <|
  .seq (.atom (.arithmetic .mul destination Reserve.factorRegister Reserve.precision))
       (.atom (.arithmetic .add destination destination Reserve.base))
def state (data : Data) (destination : Fin 128) (slot : ℕ) : Data :=
  ((data.set Reserve.factorRegister slot).set destination (slot*data.1 Reserve.precision)).set destination
    (data.1 Reserve.base+slot*data.1 Reserve.precision)

attribute [local simp] Reserve.factorRegister Reserve.precision Reserve.base NaturalData.set

theorem program_exec {w : ℕ} (data : Data) (destination : Fin 128) (slot : ℕ)
    (precision_ne : destination≠Reserve.precision) (base_ne : destination≠Reserve.base)
    (slotFits : Fits w slot) (productFits : Fits w (slot*data.1 Reserve.precision : ℕ))
    (addressFits : Fits w (data.1 Reserve.base+slot*data.1 Reserve.precision : ℕ)) :
    NaturalData.Exec w (program destination slot) data (state data destination slot) 3 := by
  have a := NaturalData.constant_exec data Reserve.factorRegister slot slotFits
  have b := NaturalData.mul_exec (data.set Reserve.factorRegister slot) destination Reserve.factorRegister Reserve.precision
    (by simpa using productFits)
  have c := NaturalData.add_exec ((data.set Reserve.factorRegister slot).set destination (slot*data.1 Reserve.precision))
    destination destination Reserve.base
    (by simpa [Ne.symm base_ne,Nat.add_comm] using addressFits)
  simpa [program,state,NaturalData.set,Ne.symm base_ne,Nat.add_comm] using a.seq (b.seq c)

@[simp] theorem state_destination (data : Data) (destination : Fin 128) (slot : ℕ) :
    (state data destination slot).1 destination=data.1 Reserve.base+slot*data.1 Reserve.precision := by simp [state]
@[simp] theorem state_memory (data : Data) (destination : Fin 128) (slot : ℕ) :
    (state data destination slot).2=data.2 := rfl

theorem state_other (data : Data) (destination : Fin 128) (slot : ℕ) (i : Fin 128)
    (notDest : i≠destination) (notScratch : i≠Reserve.factorRegister) :
    (state data destination slot).1 i=data.1 i := by
  simp only [state,NaturalData.set,Function.update_of_ne notDest,Function.update_of_ne notScratch]

end LeanTrominoes.Domino.WordRAM.Binary.HeaderPointer

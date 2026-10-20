/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMProbe

/-! # Moving an original binary field into a circuit input slot -/
namespace LeanTrominoes.Domino.WordRAM.Binary.BlockCopy
open ComplexityAbstract.RAM
abbrev Data := NaturalData 64
abbrev Code := Structured.Code 64
abbrev lengthRegister : Fin 64 := 56
abbrev sourceRegister : Fin 64 := 57
abbrev targetRegister : Fin 64 := 58
abbrev low (i : Fin 16) : Fin 64 := i.castAdd 48

def pointerProgram (destination : Fin 16) (base : Fin 64) (slot : ℕ) : Code :=
  .seq (.atom (.constant (low Reg.left) slot)) <|
  .seq (.atom (.arithmetic .mul (low destination) (low Reg.left) (low Reg.length)))
    (.atom (.arithmetic .add (low destination) (low destination) base))

def pointerState (data : Data) (destination : Fin 16) (base : Fin 64) (slot : ℕ) : Data :=
  ((data.set (low Reg.left) slot).set (low destination) (slot*data.1 (low Reg.length))).set
    (low destination) (slot*data.1 (low Reg.length)+data.1 base)

def setup (sourceSlot targetSlot : ℕ) : Code :=
  .seq (.atom (.copy (low Reg.length) lengthRegister)) <|
  .seq (pointerProgram Reg.first sourceRegister sourceSlot) (pointerProgram Reg.output targetRegister targetSlot)

def prepared (data : Data) (sourceSlot targetSlot : ℕ) : Data :=
  pointerState (pointerState (data.set (low Reg.length) (data.1 lengthRegister)) Reg.first sourceRegister sourceSlot)
    Reg.output targetRegister targetSlot

def program (sourceSlot targetSlot : ℕ) : Code :=
  .seq (setup sourceSlot targetSlot) (copyProgram.embed 48)

attribute [local simp] Reg.first Reg.output Reg.left Reg.length lengthRegister sourceRegister targetRegister low NaturalData.set

private theorem pointer_exec {w : ℕ} (data : Data) (destination : Fin 16) (base : Fin 64) (slot : ℕ)
    (different : destination≠Reg.length) (high : 16≤ base.val)
    (slotFits : Fits w slot) (productFits : Fits w (slot*data.1 (low Reg.length) : ℕ))
    (addressFits : Fits w (slot*data.1 (low Reg.length)+data.1 base : ℕ)) :
    NaturalData.Exec w (pointerProgram destination base slot) data (pointerState data destination base slot) 3 := by
  have baseNeLeft : base≠low Reg.left := by intro equal; have := congrArg Fin.val equal; simp at this; omega
  have baseNeDst : base≠low destination := by
    intro equal
    have val := congrArg Fin.val equal
    have := destination.isLt
    simp only [low,Fin.val_castAdd] at val
    omega
  have dstNeLength : low Reg.length≠low destination := by
    intro equal
    exact different (Fin.castAdd_inj.mp equal).symm
  have one := NaturalData.constant_exec data (low Reg.left) slot slotFits
  have two := NaturalData.mul_exec (data.set (low Reg.left) slot) (low destination) (low Reg.left) (low Reg.length)
    (by simpa using productFits)
  have three := NaturalData.add_exec ((data.set (low Reg.left) slot).set (low destination) (slot*data.1 (low Reg.length)))
    (low destination) (low destination) base (by simpa only [NaturalData.set,Function.update_self,Function.update_of_ne baseNeDst,Function.update_of_ne baseNeLeft] using addressFits)
  simpa only [pointerProgram,pointerState,NaturalData.set,Function.update_self,
    Function.update_of_ne baseNeDst,Function.update_of_ne baseNeLeft] using one.seq (two.seq three)

theorem program_exec {w : ℕ} (data : Data) (source target length sourceSlot targetSlot : ℕ)
    (length_eq : data.1 lengthRegister=length) (source_eq : data.1 sourceRegister=source)
    (target_eq : data.1 targetRegister=target)
    (safe : ∀ i< length, ∀ j< length, i< j → target+targetSlot*length+i≠source+sourceSlot*length+j)
    (bits : ∀ i< length, data.2 (source+sourceSlot*length+i)≤1)
    (oneFits : Fits w (1:ℕ)) (lengthFits : Fits w length)
    (sourceSlotFits : Fits w sourceSlot) (targetSlotFits : Fits w targetSlot)
    (sourceProductFits : Fits w (sourceSlot*length : ℕ)) (targetProductFits : Fits w (targetSlot*length : ℕ))
    (sourceFits : Fits w (source+sourceSlot*length+length : ℕ))
    (targetFits : Fits w (target+targetSlot*length+length : ℕ)) :
    ∃ result, NaturalData.Exec w (program sourceSlot targetSlot) data result (7*length+11) ∧
      CopyRepresents ⟨source+sourceSlot*length,target+targetSlot*length,length,safe⟩ data.2 length
        (NaturalData.lower (r:=16) (s:=48) result) ∧
      (∀ i : Fin 64, 16≤ i.val → result.1 i=data.1 i) := by
  have sourceAddress : Fits w (sourceSlot*length+source : ℕ) := by
    refine ⟨sourceFits.1,?_,lt_of_le_of_lt (by exact_mod_cast show sourceSlot*length+source≤ source+sourceSlot*length+length by omega) sourceFits.2.2⟩
    exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)
  have targetAddress : Fits w (targetSlot*length+target : ℕ) := by
    refine ⟨targetFits.1,?_,lt_of_le_of_lt (by exact_mod_cast show targetSlot*length+target≤ target+targetSlot*length+length by omega) targetFits.2.2⟩
    exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)
  have a := NaturalData.copy_exec data (low Reg.length) lengthRegister (by rw [length_eq]; exact lengthFits)
  have b := pointer_exec (data.set (low Reg.length) (data.1 lengthRegister)) Reg.first sourceRegister sourceSlot
    (by decide) (by decide) sourceSlotFits (by simpa [length_eq] using sourceProductFits)
    (by simpa [length_eq,source_eq] using sourceAddress)
  have c := pointer_exec (pointerState (data.set (low Reg.length) (data.1 lengthRegister)) Reg.first sourceRegister sourceSlot)
    Reg.output targetRegister targetSlot (by decide) (by decide) targetSlotFits
    (by simpa [pointerState,length_eq] using targetProductFits)
    (by simpa [pointerState,length_eq,target_eq] using targetAddress)
  have setupRun : NaturalData.Exec w (setup sourceSlot targetSlot) data (prepared data sourceSlot targetSlot) 7 := a.seq (b.seq c)
  obtain ⟨small,copyRun,correct⟩ := copyProgram_exec
    ⟨source+sourceSlot*length,target+targetSlot*length,length,safe⟩
    (NaturalData.lower (r:=16) (s:=48) (prepared data sourceSlot targetSlot))
    (by simp [NaturalData.lower,prepared,pointerState,length_eq])
    (by simp [NaturalData.lower,prepared,pointerState,length_eq,source_eq,Nat.add_comm])
    (by simp [NaturalData.lower,prepared,pointerState,length_eq,target_eq,Nat.add_comm])
    bits oneFits sourceFits targetFits lengthFits
  have call := NaturalData.call_exec (r:=16) (s:=48) copyRun
  have full := setupRun.seq call
  change NaturalData.Exec w (program sourceSlot targetSlot) data _ (7+(7*length+4)) at full
  refine ⟨_,by convert full using 1 <;> omega,?_,?_⟩
  · simpa only [NaturalData.lower_extend] using (show CopyRepresents _ data.2 length small from correct)
  intro i high
  let j : Fin 48 := ⟨i.val-16,by have := i.isLt; omega⟩
  have same : j.natAdd 16=i := by apply Fin.ext; simp only [Fin.val_natAdd]; dsimp [j]; omega
  rw [←same,NaturalData.extend_right]
  change (prepared data sourceSlot targetSlot).1 (j.natAdd 16)=data.1 (j.natAdd 16)
  rw [same]
  have ne (reg : Fin 16) : i≠low reg := by
    intro equal
    have val := congrArg Fin.val equal
    have := reg.isLt
    simp only [low,Fin.val_castAdd] at val
    omega
  simp only [prepared,pointerState,NaturalData.set,Function.update_of_ne (ne Reg.output),
    Function.update_of_ne (ne Reg.left),Function.update_of_ne (ne Reg.first),Function.update_of_ne (ne Reg.length)]

end LeanTrominoes.Domino.WordRAM.Binary.BlockCopy

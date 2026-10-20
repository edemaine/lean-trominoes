/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMBlockCopy

/-! # A fixed sequence copying consecutive original input fields -/
namespace LeanTrominoes.Domino.WordRAM.Binary.BatchCopy
open ComplexityAbstract.RAM
abbrev Data := BlockCopy.Data
abbrev Code := BlockCopy.Code

def program : ℕ → ℕ → ℕ → Code
  | 0, _, _ => .atom (.copy BlockCopy.lengthRegister BlockCopy.lengthRegister)
  | count+1, first, target => .seq (BlockCopy.program first target) (program count (first+1) (target+1))

def bound (source target length sourceStart targetStart count : ℕ) : ℕ :=
  source+(sourceStart+count+1)*(length+1)+target+(targetStart+count+1)*(length+1)+length+3

structure Result (source target length sourceStart targetStart count : ℕ)
    (memory : ℕ → ℕ) (data : Data) : Prop where
  copied : ∀ j< count, ∀ i< length,
    data.2 (target+(targetStart+j)*length+i)=memory (source+(sourceStart+j)*length+i)
  frame : ∀ address, (address< target+targetStart*length ∨ target+(targetStart+count)*length≤ address) →
    data.2 address=memory address

private theorem outside {source target length sourceStart targetStart count j i : ℕ}
    (different : ∀ a< count, ∀ b< count, ∀ x< length, ∀ y< length,
      source+(sourceStart+a)*length+x≠target+(targetStart+b)*length+y)
    (hj : j< count) (hi : i< length) :
    source+(sourceStart+j)*length+i< target+targetStart*length ∨
      target+(targetStart+count)*length≤ source+(sourceStart+j)*length+i := by
  by_contra h
  push Not at h
  have positive : 0< length := by omega
  let offset := source+(sourceStart+j)*length+i-(target+targetStart*length)
  have split : offset+(target+targetStart*length)=source+(sourceStart+j)*length+i := Nat.sub_add_cancel h.1
  have expanded : target+(targetStart+count)*length=target+targetStart*length+count*length := by ring
  have off : offset< count*length := by rw [expanded] at h; omega
  have q : offset/length< count := (Nat.div_lt_iff_lt_mul positive).mpr off
  have rem : offset%length< length := Nat.mod_lt _ positive
  have diseq := different j hj (offset/length) q i hi (offset%length) rem
  have decomp := Nat.mod_add_div offset length
  have equal : source+(sourceStart+j)*length+i=target+(targetStart+offset/length)*length+offset%length := by
    nlinarith only [split,decomp]
  exact diseq equal

private theorem digits_equal (firstMemory secondMemory : ℕ → ℕ) (first second length : ℕ)
    (firstBits : ∀ i< length, firstMemory (first+i)≤1)
    (secondBits : ∀ i< length, secondMemory (second+i)≤1)
    (equal : value firstMemory first length=value secondMemory second length) :
    ∀ i< length, firstMemory (first+i)=secondMemory (second+i) := by
  induction length generalizing first second with
  | zero => simp
  | succ length ih =>
    rw [value_head firstMemory first length,value_head secondMemory second length] at equal
    have a := firstBits 0 (by omega)
    have b := secondBits 0 (by omega)
    simp only [Nat.add_zero] at a b
    have head : firstMemory first=secondMemory second := by omega
    have tails : value firstMemory (first+1) length=value secondMemory (second+1) length := by omega
    have rest := ih (first+1) (second+1)
      (fun i hi => by simpa [Nat.add_assoc,Nat.add_comm 1 i] using firstBits (i+1) (by omega))
      (fun i hi => by simpa [Nat.add_assoc,Nat.add_comm 1 i] using secondBits (i+1) (by omega)) tails
    intro i hi
    cases i with
    | zero => simpa using head
    | succ i => simpa [Nat.add_assoc,Nat.add_comm 1 i] using rest i (by omega)

theorem program_exec {w : ℕ} (source target length count : ℕ) :
    ∀ sourceStart targetStart data,
    data.1 BlockCopy.lengthRegister=length → data.1 BlockCopy.sourceRegister=source →
    data.1 BlockCopy.targetRegister=target →
    (∀ a< count, ∀ b< count, ∀ x< length, ∀ y< length,
      source+(sourceStart+a)*length+x≠target+(targetStart+b)*length+y) →
    (∀ j< count, ∀ i< length, data.2 (source+(sourceStart+j)*length+i)≤1) →
    Fits w (bound source target length sourceStart targetStart count) →
    ∃ result, NaturalData.Exec w (program count sourceStart targetStart) data result ((7*length+11)*count+1) ∧
      Result source target length sourceStart targetStart count data.2 result ∧
      (∀ i : Fin 64, 16≤ i.val → result.1 i=data.1 i) := by
  induction count with
  | zero =>
    intro sourceStart targetStart data length_eq source_eq target_eq different bits fits
    have lengthFits : Fits w (data.1 BlockCopy.lengthRegister) := by
      rw [length_eq]
      exact Allocation.nat_fits_le fits (by unfold bound; omega)
    have run := NaturalData.copy_exec data BlockCopy.lengthRegister BlockCopy.lengthRegister lengthFits
    refine ⟨data,?_,⟨by simp,fun _ _ => rfl⟩,fun _ _ => rfl⟩
    simpa [program,NaturalData.set] using run
  | succ count ih =>
    intro sourceStart targetStart data length_eq source_eq target_eq different bits fits
    have smallFits (n : ℕ) (h : n≤ bound source target length sourceStart targetStart (count+1)) : Fits w n :=
      Allocation.nat_fits_le fits h
    obtain ⟨middle,firstRun,firstResult,firstRegisters⟩ := BlockCopy.program_exec data source target length sourceStart targetStart
      length_eq source_eq target_eq (fun i hi j hj _ => (different 0 (by omega) 0 (by omega) j hj i hi).symm)
      (by simpa using bits 0 (by omega))
      (smallFits 1 (by unfold bound; nlinarith)) (smallFits length (by unfold bound; nlinarith))
      (smallFits sourceStart (by unfold bound; nlinarith)) (smallFits targetStart (by unfold bound; nlinarith))
      (smallFits (sourceStart*length) (by unfold bound; nlinarith)) (smallFits (targetStart*length) (by unfold bound; nlinarith))
      (smallFits (source+sourceStart*length+length) (by unfold bound; nlinarith))
      (smallFits (target+targetStart*length+length) (by unfold bound; nlinarith))
    have preserved (j : ℕ) (hj : j< count+1) (i : ℕ) (hi : i< length) :
        middle.2 (source+(sourceStart+j)*length+i)=data.2 (source+(sourceStart+j)*length+i) := by
      apply firstResult.frame
      have h := outside different hj hi
      rcases h with before | after
      · exact Or.inl before
      · right
        nlinarith
    obtain ⟨result,restRun,restResult,restRegisters⟩ := ih (sourceStart+1) (targetStart+1) middle
      (by rw [firstRegisters _ (by decide)]; exact length_eq)
      (by rw [firstRegisters _ (by decide)]; exact source_eq)
      (by rw [firstRegisters _ (by decide)]; exact target_eq)
      (by intro a ha b hb x hx y hy; simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using different (a+1) (by omega) (b+1) (by omega) x hx y hy)
      (by intro j hj i hi; have p := preserved (j+1) (by omega) i hi; have b := bits (j+1) (by omega) i hi
          simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using p.trans_le b)
      (by convert fits using 1 <;> unfold bound <;> ring)
    refine ⟨result,?_,?_,fun i hi => (restRegisters i hi).trans (firstRegisters i hi)⟩
    · have cost : (7*length+11)*(count+1)+1=(7*length+11)+((7*length+11)*count+1) := by ring
      rw [cost]
      exact firstRun.seq restRun
    · constructor
      · intro j hj i hi
        cases j with
        | zero =>
          have after : result.2 (target+targetStart*length+i)=middle.2 (target+targetStart*length+i) := by
            apply restResult.frame
            left
            nlinarith
          simp only [Nat.add_zero]
          rw [after]
          exact digits_equal middle.2 data.2 (target+targetStart*length) (source+sourceStart*length) length
            firstResult.output_bits (bits 0 (by omega)) firstResult.result i hi
        | succ j =>
          have equal := restResult.copied j (by omega) i hi
          have orig := preserved (j+1) (by omega) i hi
          simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at equal orig ⊢
          exact equal.trans orig
      · intro address h
        have restOutside : address< target+(targetStart+1)*length ∨
            target+((targetStart+1)+count)*length≤ address := by
          rcases h with before | after
          · left; nlinarith
          · right; nlinarith
        rw [restResult.frame address restOutside]
        apply firstResult.frame
        rcases h with before | after
        · left; exact before
        · right; nlinarith

end LeanTrominoes.Domino.WordRAM.Binary.BatchCopy

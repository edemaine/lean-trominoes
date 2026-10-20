/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSourceLoad

/-! # The source loader establishes the circuit's complete input invariant -/
namespace LeanTrominoes.Domino.WordRAM.Binary.SourceLoad
open ComplexityAbstract.RAM

theorem slot_within (d : ℕ) (block : Fin 3) (slot : ℕ) (within : slot< count d block) :
    start d block+slot< d*d+2*d := by fin_cases block <;> norm_num [start,count,Circuit.slotBase] at within ⊢ <;> omega

def inputIndex (d : ℕ) (block : Fin 3) (slot : ℕ) (within : slot< count d block) : Fin (d*d+2*d) :=
  ⟨start d block+slot,slot_within d block slot within⟩

theorem slot_cover (d slot : ℕ) (within : slot< d*d+2*d) :
    ∃ block : Fin 3, ∃ offset, offset< count d block ∧ slot=start d block+offset := by
  by_cases basis : slot< d*d
  · exact ⟨0,slot,by simpa [count] using basis,by simp [start]⟩
  by_cases first : slot< d*d+d
  · exact ⟨1,slot-d*d,by norm_num [count]; omega,by norm_num [start]; omega⟩
  · exact ⟨2,slot-(d*d+d),by norm_num [count]; omega,by norm_num [start]; omega⟩

def readyCode : Code :=
  .seq (.atom (.copy (BlockCopy.low Reg.length) SourceBlocks.precision))
       (.atom (.copy (Circuit.baseRegister.castAdd 47) SourceBlocks.circuitBase))
def ready (data : Data) : Data :=
  (data.set (BlockCopy.low Reg.length) (data.1 SourceBlocks.precision)).set
    (Circuit.baseRegister.castAdd 47) (data.1 SourceBlocks.circuitBase)
def completeProgram (d : ℕ) : Code := .seq (program d) readyCode

theorem ready_exec {w : ℕ} (data : Data)
    (lengthFits : Fits w (data.1 SourceBlocks.precision)) (baseFits : Fits w (data.1 SourceBlocks.circuitBase)) :
    NaturalData.Exec w readyCode data (ready data) 2 := by
  have a := NaturalData.copy_exec data (BlockCopy.low Reg.length) SourceBlocks.precision lengthFits
  have b := NaturalData.copy_exec (data.set (BlockCopy.low Reg.length) (data.1 SourceBlocks.precision))
    (Circuit.baseRegister.castAdd 47) SourceBlocks.circuitBase
    (by simpa [NaturalData.set,BlockCopy.low,Reg.length,SourceBlocks.circuitBase] using baseFits)
  simpa [readyCode,ready,NaturalData.set,BlockCopy.low,Reg.length,SourceBlocks.circuitBase] using a.seq b

theorem Result.represents {p : Layout} {source : ℕ → ℕ} {data : Data}
    (h : Result p source data) (inputs : Fin (p.dimension*p.dimension+2*p.dimension) → ℤ)
    (bits : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
      source (p.source block+slot*p.length+i)≤1)
    (encoding : ∀ block : Fin 3, ∀ slot, ∀ within : slot< count p.dimension block,
      (value source (p.source block+slot*p.length) p.length : ℤ)=
        inputs (inputIndex p.dimension block slot within)%(2^p.length : ℕ)) :
    Circuit.Represents p.base p.length (p.dimension*p.dimension+2*p.dimension)
      (Circuit.integerValues inputs) (NaturalData.lower (r:=17) (s:=47) (ready data)) := by
  constructor
  · simpa [ready,NaturalData.lower,NaturalData.set,Circuit.baseRegister,BlockCopy.low,Reg.length] using h.controls.base
  · simpa [ready,NaturalData.lower,NaturalData.set,Circuit.baseRegister,BlockCopy.low,Circuit.low,Reg.length] using h.controls.length
  · intro slot within i hi
    obtain ⟨block,offset,ho,rfl⟩ := slot_cover p.dimension slot within
    change data.2 (p.base+(start p.dimension block+offset)*p.length+i)≤1
    rw [h.copied block offset ho i hi]
    exact bits block offset ho i hi
  · intro slot within
    obtain ⟨block,offset,ho,rfl⟩ := slot_cover p.dimension slot within
    have values : value data.2 (p.base+(start p.dimension block+offset)*p.length) p.length=
        value source (p.source block+offset*p.length) p.length :=
      by
        unfold value
        apply Finset.sum_congr rfl
        intro i hi
        rw [h.copied block offset ho i (Finset.mem_range.mp hi)]
    have encoded := encoding block offset ho
    rw [←values] at encoded
    have casted := congrArg (fun z : ℤ => (z : ZMod (2^p.length))) encoded
    rw [ZMod.intCast_mod] at casted
    change (value data.2 (p.base+(start p.dimension block+offset)*p.length) p.length : ZMod (2^p.length))=
      Circuit.integerValues inputs (start p.dimension block+offset)
    rw [Circuit.integerValues,dif_pos (slot_within p.dimension block offset ho)]
    simpa only [Int.cast_natCast,inputIndex] using casted

theorem completeProgram_exec {w : ℕ} (p : Layout) (data : Data) (controls : Controls p data)
    (outside : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
      p.source block+slot*p.length+i< p.base ∨
        p.base+(p.dimension*p.dimension+2*p.dimension)*p.length≤ p.source block+slot*p.length+i)
    (bits : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
      data.2 (p.source block+slot*p.length+i)≤1)
    (fits : ∀ block : Fin 3, Fits w (BatchCopy.bound (p.source block) p.base p.length 0
      (start p.dimension block) (count p.dimension block))) :
    ∃ result cost, NaturalData.Exec w (completeProgram p.dimension) data result cost ∧
      cost=(7*p.length+11)*(p.dimension*p.dimension+2*p.dimension)+17 ∧
      ∃ copied, Result p data.2 copied ∧ result=ready copied := by
  obtain ⟨copied,run,correct⟩ := program_exec p data controls outside bits fits
  have resource := fits 0
  have lengthFits : Fits w (copied.1 SourceBlocks.precision) := by
    rw [correct.controls.length]
    exact Allocation.nat_fits_le resource (by unfold BatchCopy.bound; omega)
  have baseFits : Fits w (copied.1 SourceBlocks.circuitBase) := by
    rw [correct.controls.base]
    exact Allocation.nat_fits_le resource (by unfold BatchCopy.bound; omega)
  refine ⟨_,_,run.seq (ready_exec copied lengthFits baseFits),by omega,copied,correct,rfl⟩

end LeanTrominoes.Domino.WordRAM.Binary.SourceLoad

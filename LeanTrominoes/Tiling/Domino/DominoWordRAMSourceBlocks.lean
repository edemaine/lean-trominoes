/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMBatchCopy

/-! # Calling a fixed field-copy batch with caller-private input pointers -/
namespace LeanTrominoes.Domino.WordRAM.Binary.SourceBlocks
open ComplexityAbstract.RAM
abbrev Data := BlockCopy.Data
abbrev Code := BlockCopy.Code
abbrev firstOrigin : Fin 64 := 59
abbrev secondOrigin : Fin 64 := 60
abbrev precision : Fin 64 := 61
abbrev circuitBase : Fin 64 := 62
abbrev basisBase : Fin 64 := 63

def moves (source : Fin 64) : List (Fin 64 × Fin 64) :=
  [(BlockCopy.lengthRegister,precision),(BlockCopy.targetRegister,circuitBase),(BlockCopy.sourceRegister,source)]
def setup (source : Fin 64) : Code := Assignments.code (BlockCopy.low Reg.length) precision (moves source)
def prepared (source : Fin 64) (data : Data) : Data := Assignments.state (BlockCopy.low Reg.length) precision (moves source) data

def program (source : Fin 64) (count targetSlot : ℕ) : Code :=
  .seq (setup source) (BatchCopy.program count 0 targetSlot)

attribute [local simp] BlockCopy.lengthRegister BlockCopy.sourceRegister BlockCopy.targetRegister
  BlockCopy.low Reg.length precision circuitBase NaturalData.set

theorem setup_exec {w : ℕ} (data : Data) (source : Fin 64) (high : 59≤ source.val)
    (lengthFits : Fits w (data.1 precision)) (targetFits : Fits w (data.1 circuitBase))
    (sourceFits : Fits w (data.1 source)) :
    NaturalData.Exec w (setup source) data (prepared source data) 4 := by
  apply Assignments.exec data (BlockCopy.low Reg.length) precision (moves source) lengthFits
  · intro p hp
    simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact lengthFits
    · exact targetFits
    · exact sourceFits
  · intro p hp q hq
    simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp
    all_goals intro same; have equal := congrArg Fin.val same; change _=source.val at equal; omega
  · simp [moves]

theorem prepared_args (data : Data) (source : Fin 64) (high : 59≤ source.val) :
    (prepared source data).1 BlockCopy.lengthRegister=data.1 precision ∧
    (prepared source data).1 BlockCopy.sourceRegister=data.1 source ∧
    (prepared source data).1 BlockCopy.targetRegister=data.1 circuitBase := by
  have different (i : Fin 64) (small : i.val<59) : i≠source := by intro eq; have := congrArg Fin.val eq; omega
  have ne56 : source≠56 := by intro eq; have := congrArg Fin.val eq; simp at this; omega
  have ne58 : source≠58 := by intro eq; have := congrArg Fin.val eq; simp at this; omega
  simp [prepared,Assignments.state,moves,ne56,ne58]

theorem prepared_high (data : Data) (source i : Fin 64) (high : 59≤ i.val) :
    (prepared source data).1 i=data.1 i := by
  have ne (j : Fin 64) (small : j.val<59) : i≠j := by intro eq; have := congrArg Fin.val eq; omega
  simp only [prepared,Assignments.state,moves,List.foldl_cons,List.foldl_nil,NaturalData.set,
    Function.update_of_ne (ne (BlockCopy.low Reg.length) (by decide)),
    Function.update_of_ne (ne BlockCopy.sourceRegister (by decide)),
    Function.update_of_ne (ne BlockCopy.targetRegister (by decide)),
    Function.update_of_ne (ne BlockCopy.lengthRegister (by decide))]

theorem program_exec {w : ℕ} (data : Data) (source : Fin 64) (high : 59≤ source.val)
    (count targetSlot : ℕ)
    (separate : ∀ a< count, ∀ b< count, ∀ x< data.1 precision, ∀ y< data.1 precision,
      data.1 source+a*data.1 precision+x≠data.1 circuitBase+(targetSlot+b)*data.1 precision+y)
    (bits : ∀ j< count, ∀ i< data.1 precision, data.2 (data.1 source+j*data.1 precision+i)≤1)
    (fits : Fits w (BatchCopy.bound (data.1 source) (data.1 circuitBase) (data.1 precision) 0 targetSlot count)) :
    ∃ result, NaturalData.Exec w (program source count targetSlot) data result
        (4+((7*data.1 precision+11)*count+1)) ∧
      BatchCopy.Result (data.1 source) (data.1 circuitBase) (data.1 precision) 0 targetSlot count data.2 result ∧
      (∀ i : Fin 64, 59≤ i.val → result.1 i=data.1 i) := by
  have lengthFits := Allocation.nat_fits_le fits (show data.1 precision≤ BatchCopy.bound _ _ _ _ _ _ by unfold BatchCopy.bound; omega)
  have sourceFits := Allocation.nat_fits_le fits (show data.1 source≤ BatchCopy.bound _ _ _ _ _ _ by unfold BatchCopy.bound; omega)
  have targetFits := Allocation.nat_fits_le fits (show data.1 circuitBase≤ BatchCopy.bound _ _ _ _ _ _ by unfold BatchCopy.bound; omega)
  have args := prepared_args data source high
  obtain ⟨result,run,correct,registers⟩ := BatchCopy.program_exec (data.1 source) (data.1 circuitBase) (data.1 precision) count 0 targetSlot
    (prepared source data) args.1 args.2.1 args.2.2
    (by simpa using separate) (by change ∀ j<count, ∀ i<data.1 precision, data.2 (data.1 source+(0+j)*data.1 precision+i)≤1; simpa using bits) fits
  refine ⟨result,(setup_exec data source high lengthFits targetFits sourceFits).seq run,correct,?_⟩
  intro i hi
  rw [registers i (by omega)]
  exact prepared_high data source i hi

end LeanTrominoes.Domino.WordRAM.Binary.SourceBlocks

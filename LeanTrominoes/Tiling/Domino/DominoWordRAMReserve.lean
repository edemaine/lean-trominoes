/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRawProbe
import LeanTrominoes.Computation.RAM.NaturalAllocation

/-! # Fresh, explicitly cleared decoder workspace -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Reserve
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
abbrev precision : Fin 128 := 72
abbrev frontier : Fin 128 := 74
abbrev base : Fin 128 := 81
abbrev factorRegister : Fin 128 := 6

def setup (factor : ℕ) : Code :=
  .seq (.atom (.constant factorRegister factor)) <|
  .seq (.atom (.arithmetic .mul (Allocation.count 122) factorRegister precision))
       (.atom (.copy (Allocation.frontier 122) frontier))
def prepared (data : Data) (factor : ℕ) : Data :=
  ((data.set factorRegister factor).set (Allocation.count 122) (factor*data.1 precision)).set
    (Allocation.frontier 122) (data.1 frontier)
def save : Code :=
  .seq (.atom (.copy frontier (Allocation.frontier 122))) (.atom (.copy base (Allocation.result 122)))
def saved (data : Data) : Data :=
  (data.set frontier (data.1 (Allocation.frontier 122))).set base (data.1 (Allocation.result 122))
def program (factor : ℕ) : Code := .seq (setup factor) <| .seq (Allocation.program 122) save

theorem clear_apply (memory : ℕ → ℕ) (base length address : ℕ) :
    NaturalData.clear memory base length address=if base≤ address ∧ address< base+length then 0 else memory address := by
  have cast := Allocation.clear_apply (fun a => (memory a : ℤ)) base length address
  rw [←NaturalData.clear_word] at cast
  dsimp only at cast
  split_ifs at cast ⊢ <;> exact_mod_cast cast

attribute [local simp] precision frontier base factorRegister Allocation.count Allocation.frontier Allocation.result
  Allocation.cursor Allocation.zero Allocation.one NaturalData.set

theorem program_exec {w : ℕ} (data : Data) (factor : ℕ)
    (factorFits : Fits w factor) (requestFits : Fits w (factor*data.1 precision : ℕ))
    (endpointFits : Fits w (data.1 frontier+factor*data.1 precision : ℕ)) (unit : Fits w (1:ℕ)) :
    ∃ result, NaturalData.Exec w (program factor) data result (4*(factor*data.1 precision)+12) ∧
      result.1 frontier=data.1 frontier+factor*data.1 precision ∧ result.1 base=data.1 frontier ∧
      result.2=NaturalData.clear data.2 (data.1 frontier) (factor*data.1 precision) ∧
      (∀ i : Fin 128, 7≤ i.val → i≠frontier → i≠base → result.1 i=data.1 i) ∧
      result=saved ((prepared data factor).allocated (data.1 frontier) (factor*data.1 precision)) := by
  have a := NaturalData.constant_exec data factorRegister factor factorFits
  have b := NaturalData.mul_exec (data.set factorRegister factor) (Allocation.count 122) factorRegister precision
    (by simpa using requestFits)
  have frontFits : Fits w (data.1 frontier) := Allocation.nat_fits_le endpointFits (Nat.le_add_right _ _)
  have c := NaturalData.copy_exec ((data.set factorRegister factor).set (Allocation.count 122) (factor*data.1 precision))
    (Allocation.frontier 122) frontier (by simpa using frontFits)
  have initRun : NaturalData.Exec w (setup factor) data (prepared data factor) 3 := by
    simpa [setup,prepared] using a.seq (b.seq c)
  have alloc := NaturalData.allocate_exec (r:=122) (prepared data factor) (data.1 frontier) (factor*data.1 precision)
    (by simp [prepared]) (by simp [prepared]) endpointFits unit
  let allocated := (prepared data factor).allocated (data.1 frontier) (factor*data.1 precision)
  have savedFront : allocated.1 (Allocation.frontier 122)=data.1 frontier+factor*data.1 precision := by
    simp [allocated,NaturalData.allocated,NaturalData.allocatedRegisters]
  have savedBase : allocated.1 (Allocation.result 122)=data.1 frontier := by
    simp [allocated,NaturalData.allocated,NaturalData.allocatedRegisters]
  have d := NaturalData.copy_exec allocated frontier (Allocation.frontier 122) (by rw [savedFront]; exact endpointFits)
  have e := NaturalData.copy_exec (allocated.set frontier (allocated.1 (Allocation.frontier 122))) base (Allocation.result 122)
    (by dsimp only [NaturalData.set]; rw [Function.update_of_ne (show Allocation.result 122≠frontier by decide),savedBase]; exact frontFits)
  have finish : NaturalData.Exec w save allocated (saved allocated) 2 := by
    simpa [save,saved] using d.seq e
  refine ⟨saved allocated,?_,?_,?_,rfl,?_,rfl⟩
  · have full := initRun.seq (alloc.seq finish)
    change NaturalData.Exec w (program factor) data (saved allocated) (3+((4*(factor*data.1 precision)+7)+2)) at full
    convert full using 1 <;> omega
  · simpa only [saved,NaturalData.set,Function.update_of_ne (show frontier≠base by decide),Function.update_self] using savedFront
  · simpa only [saved,NaturalData.set,Function.update_self] using savedBase
  · intro i high notFront notBase
    have ne (n : Fin 128) (low : n.val<7) : i≠n := by intro equal; have := congrArg Fin.val equal; omega
    simp only [saved,NaturalData.set,Function.update_of_ne notBase,Function.update_of_ne notFront]
    simp only [allocated,NaturalData.allocated,NaturalData.allocatedRegisters]
    rw [if_neg (ne _ (by decide)),if_neg (ne _ (by decide)),if_neg (ne _ (by decide)),
      if_neg (ne _ (by decide)),if_neg (ne _ (by decide)),if_neg (ne _ (by decide))]
    simp only [prepared,NaturalData.set,Function.update_of_ne (ne (Allocation.frontier 122) (by decide)),
      Function.update_of_ne (ne (Allocation.count 122) (by decide)),Function.update_of_ne (ne factorRegister (by decide))]

end LeanTrominoes.Domino.WordRAM.Binary.Reserve

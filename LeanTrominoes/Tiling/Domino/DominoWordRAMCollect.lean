/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMFreshCall

/-! # Collecting the coordinate parity bits and conjunction of lattice tests -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Collect
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
abbrev valid : Fin 128 := Numerator.G.valid.castAdd 64
abbrev parity : Fin 128 := Numerator.G.parity.castAdd 64
abbrev parities : Fin 128 := 67
abbrev active : Fin 128 := 68
abbrev zero : Fin 128 := 112
abbrev index : Fin 128 := 113
abbrev address : Fin 128 := 114

def choose : Code := .branch (.lt zero valid) (.atom (.copy active active)) (.atom (.constant active 0))
def program (coordinate : ℕ) : Code :=
  .seq (.atom (.constant zero 0)) <|
  .seq choose <|
  .seq (.atom (.constant index coordinate)) <|
  .seq (.atom (.arithmetic .add address parities index)) (.atom (.store address parity))

def selected (data : Data) : Data :=
  (data.set zero 0).set active (if 0< data.1 valid then data.1 active else 0)
def prepared (data : Data) (coordinate : ℕ) : Data :=
  ((selected data).set index coordinate).set address (data.1 parities+coordinate)
def result (data : Data) (coordinate : ℕ) : Data :=
  (prepared data coordinate).store (data.1 parities+coordinate) (data.1 parity)

attribute [local simp] valid parity Numerator.G.valid Numerator.G.parity parities active zero index address
  NaturalData.set NaturalData.store

private theorem fits_bit {w n : ℕ} (fits : Fits w (1:ℕ)) (bit : n≤1) : Fits w n :=
  Allocation.nat_fits_le fits bit

theorem program_exec {w : ℕ} (data : Data) (coordinate : ℕ)
    (activeBit : data.1 active≤1) (parityBit : data.1 parity≤1)
    (unit : Fits w (1:ℕ)) (coordinateFits : Fits w coordinate)
    (addressFits : Fits w (data.1 parities+coordinate : ℕ)) :
    ∃ cost, NaturalData.Exec w (program coordinate) data (result data coordinate) cost ∧ cost≤7 := by
  have fitsZero : Fits w (0:ℕ) := Allocation.nat_fits_le unit (by omega)
  have initRun := NaturalData.constant_exec data zero 0 fitsZero
  have chosen : ∃ cost, NaturalData.Exec w choose (data.set zero 0) (selected data) cost ∧ cost≤3 := by
    by_cases yes : 0< data.1 valid
    · have condition : (Structured.Condition.lt zero valid).Holds (data.set zero 0).word := by
        simpa [Structured.Condition.Holds,NaturalData.word] using (show (0:ℤ)< data.1 valid by exact_mod_cast yes)
      have copied := NaturalData.copy_exec (data.set zero 0) active active
        (by simpa using fits_bit unit activeBit)
      refine ⟨2,?_,by omega⟩
      change 0<data.1 (52:Fin 128) at yes
      simp only [selected,if_pos yes]
      simpa [choose,selected,valid,Numerator.G.valid,yes] using Structured.Exec.branch_yes (no:=.atom (.constant active 0)) condition copied
    · have condition : ¬(Structured.Condition.lt zero valid).Holds (data.set zero 0).word := by
        simpa [Structured.Condition.Holds,NaturalData.word] using (show ¬(0:ℤ)< data.1 valid by exact_mod_cast yes)
      have cleared := NaturalData.constant_exec (data.set zero 0) active 0 fitsZero
      refine ⟨3,?_,by omega⟩
      change ¬0<data.1 (52:Fin 128) at yes
      simp only [selected,if_neg yes]
      simpa [choose,selected,valid,Numerator.G.valid,yes] using Structured.Exec.branch_no (yes:=.atom (.copy active active)) condition cleared
  obtain ⟨branchCost,branchRun,branchBound⟩ := chosen
  have digitRun := NaturalData.constant_exec (selected data) index coordinate coordinateFits
  have pointerRun := NaturalData.add_exec ((selected data).set index coordinate) address parities index
    (by simpa [selected] using addressFits)
  have writeRun := NaturalData.store_exec (prepared data coordinate) address parity
    (by simpa [prepared,selected] using addressFits) (by simpa [prepared,selected] using fits_bit unit parityBit)
  have run := initRun.seq (branchRun.seq (digitRun.seq (pointerRun.seq writeRun)))
  refine ⟨1+(branchCost+(1+(1+1))),?_,by omega⟩
  simpa [program,prepared,result,selected] using run

theorem result_active (data : Data) (coordinate : ℕ) :
    (result data coordinate).1 active=if 0< data.1 valid then data.1 active else 0 := by
  simp [result,prepared,selected]

theorem result_bit (data : Data) (coordinate : ℕ) (h : data.1 active≤1) :
    (result data coordinate).1 active≤1 := by rw [result_active]; split_ifs <;> omega

theorem result_positive (data : Data) (coordinate : ℕ) :
    (0<(result data coordinate).1 active ↔ 0< data.1 active ∧ 0< data.1 valid) := by
  rw [result_active]
  split_ifs <;> omega

theorem result_memory (data : Data) (coordinate : ℕ) :
    (result data coordinate).2=Function.update data.2 (data.1 parities+coordinate) (data.1 parity) := rfl

theorem result_fixed (data : Data) (coordinate : ℕ) (i : Fin 128)
    (notActive : i≠active) (notZero : i≠zero) (notIndex : i≠index) (notAddress : i≠address) :
    (result data coordinate).1 i=data.1 i := by
  simp only [result,prepared,selected,NaturalData.set,NaturalData.store,
    Function.update_of_ne notActive,Function.update_of_ne notZero,Function.update_of_ne notIndex,
    Function.update_of_ne notAddress]

end LeanTrominoes.Domino.WordRAM.Binary.Collect

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSourceFrame

/-! # Checked source loading directly from the original input format -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM
open Binary
variable {n d : ℕ}

theorem raw_source_exec {w : ℕ} (B : BasisData n d) (u v : Fin n) (base : ℕ)
    (data : SourceLoad.Data) (controls : SourceLoad.Controls (sourceLayout B u v base) data)
    (original : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< precision B,
      data.2 ((sourceLayout B u v base).source block+slot*precision B+i)=
        inputMemory B ((sourceLayout B u v base).source block+slot*precision B+i))
    (outside : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< precision B,
      (sourceLayout B u v base).source block+slot*precision B+i< base ∨
        base+(d*d+2*d)*precision B≤(sourceLayout B u v base).source block+slot*precision B+i)
    (fits : ∀ block : Fin 3, Fits w (BatchCopy.bound ((sourceLayout B u v base).source block) base (precision B) 0
      (SourceLoad.start d block) (SourceLoad.count d block))) :
    ∃ result cost, NaturalData.Exec w (SourceLoad.completeProgram d) data result cost ∧
      cost=(7*precision B+11)*(d*d+2*d)+17 ∧
      Circuit.Represents base (precision B) (d*d+2*d) (Circuit.integerValues (rawInputs B u v))
        (NaturalData.lower (r:=17) (s:=47) result) ∧
      (∀ address, (address< base ∨ base+(d*d+2*d)*precision B≤ address) → result.2 address=data.2 address) := by
  have bits : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< precision B,
      data.2 ((sourceLayout B u v base).source block+slot*precision B+i)≤1 := by
    intro block slot hs i hi
    rw [original block slot hs i hi]
    exact sourceLayout_bits B u v base block slot hs i hi
  have encodings : ∀ block : Fin 3, ∀ slot, ∀ within : slot< SourceLoad.count d block,
      (value data.2 ((sourceLayout B u v base).source block+slot*precision B) (precision B) : ℤ)=
        rawInputs B u v (SourceLoad.inputIndex d block slot within)%(2^precision B : ℕ) := by
    intro block slot within
    rw [value_congr (original block slot within)]
    exact sourceLayout_encoding B u v base block slot within
  obtain ⟨result,cost,run,bound,copied,correct,rfl⟩ := SourceLoad.completeProgram_exec
    (sourceLayout B u v base) data controls outside bits fits
  refine ⟨_,cost,run,bound,correct.represents (rawInputs B u v) bits encodings,?_⟩
  exact correct.frame

end LeanTrominoes.Domino.WordRAM

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareSources

/-! # Loading determinant inputs from the original input memory -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

abbrev Lower (data : Data) := NaturalData.lower (r:=64) (s:=64) data
abbrev Called (result : NaturalData 64) (data : Data) := result.extend (NaturalData.upper (r:=64) (s:=64) data)

theorem called_high (result : NaturalData 64) (data : Data) (reg : Fin 128) (high : 64≤reg.val) :
    (Called result data).1 reg=data.1 reg := by
  let index : Fin 64 := ⟨reg.val-64,by have := reg.isLt; omega⟩
  have same : reg=index.natAdd 64 := by apply Fin.ext; simp [index]; omega
  rw [same,NaturalData.extend_right]
  rfl

theorem load_exec {n d w : Nat} (B : BasisData n d) (positive : 0<n)
    (data : Data) (ready : SourcesReady B data) (width : Fits w (resourceBound B)) :
    ∃ result cost, NaturalData.Exec w ((SourceLoad.completeProgram d).embed 64) data result cost ∧
      cost=(7*WordRAM.precision B+11)*(d*d+2*d)+17 ∧
      Circuit.Represents (circuitBase B) (WordRAM.precision B) (d*d+2*d)
        (Circuit.integerValues (rawInputs B ⟨0,positive⟩ ⟨0,positive⟩))
        (NaturalData.lower (r:=17) (s:=47) (Lower result)) ∧
      (∀ address, (address<circuitBase B ∨ circuitBase B+(d*d+2*d)*WordRAM.precision B≤address) →
        result.2 address=data.2 address) ∧
      (∀ reg : Fin 128, 64≤reg.val → result.1 reg=data.1 reg) := by
  let u : Fin n := ⟨0,positive⟩
  have controls : SourceLoad.Controls (sourceLayout B u u (circuitBase B)) (Lower data) := by
    constructor
    · exact ready.sourcePrecision
    · exact ready.sourceCircuit
    · intro block
      fin_cases block
      · simpa [sourceLayout,sourceRank,SourceLoad.header,Lower,NaturalData.lower,u] using ready.sourceBasis
      · simpa [sourceLayout,sourceRank,SourceLoad.header,Lower,NaturalData.lower,u] using ready.sourceFirst
      · simpa [sourceLayout,sourceRank,SourceLoad.header,Lower,NaturalData.lower,u] using ready.sourceSecond
  have original : ∀ block : Fin 3, ∀ slot<SourceLoad.count d block, ∀ i<WordRAM.precision B,
      (Lower data).2 ((sourceLayout B u u (circuitBase B)).source block+slot*WordRAM.precision B+i)=
        inputMemory B ((sourceLayout B u u (circuitBase B)).source block+slot*WordRAM.precision B+i) := by
    intro block slot within i digit
    exact ready.reserved.before _ (source_before B u u block slot within i digit)
  have outside : ∀ block : Fin 3, ∀ slot<SourceLoad.count d block, ∀ i<WordRAM.precision B,
      (sourceLayout B u u (circuitBase B)).source block+slot*WordRAM.precision B+i<circuitBase B ∨
        circuitBase B+(d*d+2*d)*WordRAM.precision B≤(sourceLayout B u u (circuitBase B)).source block+slot*WordRAM.precision B+i := by
    intro block slot within i digit
    left
    have before := source_before B u u block slot within i digit
    exact before.trans_le (by unfold circuitBase; omega)
  have fits : ∀ block : Fin 3, Fits w (BatchCopy.bound ((sourceLayout B u u (circuitBase B)).source block)
      (circuitBase B) (WordRAM.precision B) 0 (SourceLoad.start d block) (SourceLoad.count d block)) := by
    intro block
    apply Allocation.nat_fits_le width
    fin_cases block <;> norm_num [sourceLayout,sourceRank,u,SourceLoad.start,SourceLoad.count]
    all_goals unfold resourceBound; omega
  obtain ⟨result,cost,run,budget,known,frame⟩ := raw_source_exec B u u (circuitBase B) (Lower data) controls original outside fits
  refine ⟨Called result data,cost,NaturalData.call_exec (s:=64) run,budget,?_,frame,?_⟩
  · simpa only [Called,NaturalData.lower_extend] using known
  · exact called_high result data

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareSourceHeaders

/-! # Source arguments for a determinant call using the first original origin -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

def zeroUV : Code := .seq (.atom (.constant OriginPointers128.H.u 0)) (.atom (.constant OriginPointers128.H.v 0))
def zeroed (data : Data) := (data.set OriginPointers128.H.u 0).set OriginPointers128.H.v 0
noncomputable def prepareSources (d : Nat) : Code := .seq (pointersCode (pointerMoves d)) <|
  .seq zeroUV <| .seq (OriginPointers128.program d) sourceSetup

structure SourcesReady {n d : Nat} (B : BasisData n d) (data : Data) : Prop where
  reserved : Reserved B data
  zero : data.1 H.zero=inputEnd B
  determinant : data.1 H.determinant=inputEnd B+WordRAM.precision B
  twice : data.1 H.twice=inputEnd B+2*WordRAM.precision B
  parities : data.1 H.parities=inputEnd B+3*WordRAM.precision B
  firstOrigin : data.1 OriginPointers128.H.first=4+d*d*WordRAM.precision B
  secondOrigin : data.1 OriginPointers128.H.second=4+d*d*WordRAM.precision B
  sourceFirst : data.1 (low SourceBlocks.firstOrigin)=4+d*d*WordRAM.precision B
  sourceSecond : data.1 (low SourceBlocks.secondOrigin)=4+d*d*WordRAM.precision B
  sourcePrecision : data.1 (low SourceBlocks.precision)=WordRAM.precision B
  sourceCircuit : data.1 (low SourceBlocks.circuitBase)=circuitBase B
  sourceBasis : data.1 (low SourceBlocks.basisBase)=4

attribute [local simp] OriginPointers128.H.u OriginPointers128.H.v OriginPointers128.H.first OriginPointers128.H.second
  H.precision H.n H.zero H.determinant H.twice H.parities H.frontier low SourceBlocks.circuitBase NaturalData.set

theorem zeroed_fixed (data : Data) (reg : Fin 128)
    (different : reg≠OriginPointers128.H.u ∧ reg≠OriginPointers128.H.v) : (zeroed data).1 reg=data.1 reg := by
  simp only [zeroed,NaturalData.set,Function.update_of_ne different.1,Function.update_of_ne different.2]

theorem prepareSources_exec {n d w : Nat} (B : BasisData n d) (data : Data) (reserved : Reserved B data)
    (width : Fits w (resourceBound B)) :
    ∃ result, NaturalData.Exec w (prepareSources d) data result 34 ∧ SourcesReady B result := by
  let pointed := pointersState (pointerMoves d) data
  have pointers := global_pointers_exec B data reserved.base reserved.precision width
  have pointedFixed (reg : Fin 128)
      (safe : reg≠H.zero ∧ reg≠H.determinant ∧ reg≠H.twice ∧ reg≠H.parities ∧ reg≠low SourceBlocks.circuitBase ∧ reg≠Reserve.factorRegister) :
      pointed.1 reg=data.1 reg := pointed_fixed data d reg safe
  have pointedPrec : pointed.1 H.precision=WordRAM.precision B := (pointedFixed H.precision (by decide)).trans reserved.precision
  have zeroFits : Fits w (0 : Nat) := Allocation.nat_fits_le width (Nat.zero_le _)
  have zeroing : NaturalData.Exec w zeroUV pointed (zeroed pointed) 2 :=
    (NaturalData.constant_exec pointed OriginPointers128.H.u 0 zeroFits).seq
      (NaturalData.constant_exec (pointed.set OriginPointers128.H.u 0) OriginPointers128.H.v 0 zeroFits)
  have zeroedPrec : (zeroed pointed).1 OriginPointers128.H.precision=WordRAM.precision B :=
    (zeroed_fixed pointed H.precision (by decide)).trans pointedPrec
  have originFits : 4+d*d*WordRAM.precision B≤resourceBound B := (origin0_before B).trans (resource_input B)
  obtain ⟨origin,originRun,originCorrect⟩ := OriginPointers128.program_exec (d:=d) (zeroed pointed) width
    (by rw [zeroedPrec]; exact WordRAM.precision_positive B)
    (by unfold resourceBound; omega)
    (by rw [zeroedPrec]; simpa [zeroed] using originFits) (by rw [zeroedPrec]; simpa [zeroed] using originFits)
  have originFixed (reg : Fin 128) (lower : reg.val<96)
      (uNe : reg≠OriginPointers128.H.u) (vNe : reg≠OriginPointers128.H.v)
      (firstNe : reg≠OriginPointers128.H.first) (secondNe : reg≠OriginPointers128.H.second) : origin.1 reg=pointed.1 reg :=
    (originCorrect.fixed reg (Or.inl lower) firstNe secondNe).trans (zeroed_fixed pointed reg ⟨uNe,vNe⟩)
  have originPrec : origin.1 H.precision=WordRAM.precision B := (originFixed H.precision (by decide) (by decide) (by decide) (by decide) (by decide)).trans pointedPrec
  have originFirst : origin.1 OriginPointers128.H.first=4+d*d*WordRAM.precision B := by
    have first := originCorrect.first
    rw [zeroedPrec] at first
    simpa [zeroed] using first
  have originSecond : origin.1 OriginPointers128.H.second=4+d*d*WordRAM.precision B := by
    have second := originCorrect.second
    rw [zeroedPrec] at second
    simpa [zeroed] using second
  have sources := sourceSetup_exec origin
    (originPrec ▸ Allocation.nat_fits_le width (resource_precision B))
    (originFirst ▸ Allocation.nat_fits_le width originFits) (originSecond ▸ Allocation.nat_fits_le width originFits)
    (Allocation.nat_fits_le width (resource_small B))
  have high (reg : Fin 128) (lower : 64≤reg.val) (upper : reg.val<96)
      (uNe : reg≠OriginPointers128.H.u) (vNe : reg≠OriginPointers128.H.v)
      (firstNe : reg≠OriginPointers128.H.first) (secondNe : reg≠OriginPointers128.H.second) :
      (sourcePrepared origin).1 reg=pointed.1 reg := (sourcePrepared_high origin reg lower).trans
        (originFixed reg upper uNe vNe firstNe secondNe)
  have memory : (sourcePrepared origin).2=data.2 := originCorrect.memory.trans (pointersState_memory (pointerMoves d) data)
  have values := pointed_values data d
  have sourceValues := sourcePrepared_values origin
  refine ⟨sourcePrepared origin,pointers.seq (zeroing.seq (originRun.seq sources)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · rw [high H.n (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),pointedFixed H.n (by decide)]; exact reserved.n
    · rw [high H.precision (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact pointedPrec
    · rw [high Reserve.base (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),pointedFixed Reserve.base (by decide)]; exact reserved.base
    · rw [high H.frontier (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),pointedFixed H.frontier (by decide)]; exact reserved.frontier
    · exact memory.trans reserved.memory
  · rw [high H.zero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),values.1]; exact reserved.base
  · rw [high H.determinant (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),values.2.1,reserved.base,reserved.precision]
  · rw [high H.twice (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),values.2.2.1,reserved.base,reserved.precision]
  · rw [high H.parities (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),values.2.2.2.1,reserved.base,reserved.precision]
  · rw [sourcePrepared_high origin OriginPointers128.H.first (by decide)]; exact originFirst
  · rw [sourcePrepared_high origin OriginPointers128.H.second (by decide)]; exact originSecond
  · exact sourceValues.1.trans originFirst
  · exact sourceValues.2.1.trans originSecond
  · exact sourceValues.2.2.1.trans originPrec
  · rw [sourceValues.2.2.2.1,originFixed (low SourceBlocks.circuitBase) (by decide) (by decide) (by decide) (by decide) (by decide),values.2.2.2.2,reserved.base,reserved.precision]
    rfl
  · exact sourceValues.2.2.2.2

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128

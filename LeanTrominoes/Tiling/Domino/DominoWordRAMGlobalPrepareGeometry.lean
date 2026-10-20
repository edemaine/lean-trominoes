/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetup
import LeanTrominoes.Tiling.Domino.DominoWordRAMRawReady
import LeanTrominoes.Tiling.Domino.DominoWordRAMProbeHeaders
import LeanTrominoes.Tiling.Domino.DominoWordRAMOriginPointers128

/-! # One fresh global determinant workspace in the original input format -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
abbrev low (i : Fin 64) : Fin 128 := i.castAdd 64
namespace H
abbrev n : Fin 128 := 66
abbrev parities : Fin 128 := 67
abbrev precision : Fin 128 := 72
abbrev frontier : Fin 128 := 74
abbrev zero : Fin 128 := 75
abbrev determinant : Fin 128 := 76
abbrev twice : Fin 128 := 77
end H

noncomputable def factor (d : Nat) := DeterminantSetup.slots d+3+d

def inputEnd {n d : Nat} (B : BasisData n d) := (naturalWords B).length+1
noncomputable def circuitBase {n d : Nat} (B : BasisData n d) := inputEnd B+(3+d)*WordRAM.precision B
noncomputable def endAddress {n d : Nat} (B : BasisData n d) := inputEnd B+factor d*WordRAM.precision B

noncomputable def geometry {n d : Nat} (B : BasisData n d) : DeterminantSetup.Geometry d where
  base := circuitBase B
  precision := WordRAM.precision B
  zero := inputEnd B
  absolute := inputEnd B+WordRAM.precision B
  twice := inputEnd B+2*WordRAM.precision B
  auxiliary := fun i => Circuit.slotBase (inputEnd B) (WordRAM.precision B) i.val
  auxiliary_eq := by
    funext i
    fin_cases i <;> norm_num [Circuit.slotBase,Fin.ext_iff]
  disjoint := by
    intro i j different
    have ne : i.val≠j.val := by intro same; exact different (Fin.ext same)
    by_cases order : i.val<j.val
    · left
      have grow := Nat.mul_le_mul_right (WordRAM.precision B) (Nat.succ_le_of_lt order)
      unfold Circuit.slotBase
      nlinarith
    · right
      have grow := Nat.mul_le_mul_right (WordRAM.precision B) (show j.val+1≤ i.val by omega)
      unfold Circuit.slotBase
      nlinarith
  external := by
    intro i
    right
    have grow := Nat.mul_le_mul_right (WordRAM.precision B) (show i.val+1≤3+d by have := i.isLt; omega)
    unfold Circuit.slotBase circuitBase
    nlinarith

/-- A sum containing every allocation, copy and circuit operand bound.
No derived arithmetic quantity appears in the input encoding. -/
noncomputable def resourceBound {n d : Nat} (B : BasisData n d) : Nat :=
  4+n+inputEnd B+WordRAM.precision B+factor d+factor d*WordRAM.precision B+endAddress B+
    (d*d+d+4)+
    BatchCopy.bound 4 (circuitBase B) (WordRAM.precision B) 0 0 (d*d)+
    BatchCopy.bound (4+d*d*WordRAM.precision B) (circuitBase B) (WordRAM.precision B) 0 (d*d) d+
    BatchCopy.bound (4+d*d*WordRAM.precision B) (circuitBase B) (WordRAM.precision B) 0 (d*d+d) d+
    Circuit.resourceBound (circuitBase B) (WordRAM.precision B) (DeterminantSetup.slots d)

theorem resource_small {n d : Nat} (B : BasisData n d) : 4≤resourceBound B := by unfold resourceBound; omega

theorem resource_end {n d : Nat} (B : BasisData n d) : endAddress B≤resourceBound B := by unfold resourceBound; omega

theorem resource_precision {n d : Nat} (B : BasisData n d) : WordRAM.precision B≤resourceBound B := by unfold resourceBound; omega

theorem resource_input {n d : Nat} (B : BasisData n d) : inputEnd B≤resourceBound B := by unfold resourceBound; omega

theorem source_before {n d : Nat} (B : BasisData n d) (u v : Fin n) (block : Fin 3)
    (slot : Nat) (within : slot<SourceLoad.count d block) (i : Nat) (digit : i<WordRAM.precision B) :
    (sourceLayout B u v (circuitBase B)).source block+slot*WordRAM.precision B+i< inputEnd B := by
  have index := sourceRank_within B u v block slot within
  have grow := Nat.mul_le_mul_right (WordRAM.precision B) (Nat.succ_le_of_lt index)
  have length : (naturalWords B).length=3+(fields B).length*WordRAM.precision B := by
    simp [naturalWords,List.length_flatMap,integerDigits,digits_length]
    omega
  unfold inputEnd
  rw [length]
  dsimp only [sourceLayout]
  nlinarith

theorem origin0_before {n d : Nat} (B : BasisData n d) :
    4+d*d*WordRAM.precision B≤ inputEnd B := by
  have length : (naturalWords B).length=3+(d*d+n*d)*WordRAM.precision B := by
    simp [naturalWords,List.length_flatMap,integerDigits,digits_length,fields_length]
    omega
  unfold inputEnd
  rw [length]
  nlinarith [Nat.zero_le ((n*d)*WordRAM.precision B)]

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128

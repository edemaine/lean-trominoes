/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSourceReady
import LeanTrominoes.Tiling.Domino.DominoWordRAMInputTables

/-! # The circuit inputs are precisely fields of the original integer encoding -/
namespace LeanTrominoes.Domino.WordRAM
variable {n d : ℕ}
open Binary

def rawField (d u v slot : ℕ) : ℕ :=
  if slot< d*d then slot else if slot< d*d+d then d*d+u*d+(slot-d*d) else d*d+v*d+(slot-(d*d+d))

def rawInputs (B : BasisData n d) (u v : Fin n) (slot : Fin (d*d+2*d)) : ℤ :=
  ((fields B)[rawField d u.val v.val slot.val]?).getD 0

theorem rawField_within (B : BasisData n d) (u v : Fin n) (slot : ℕ) (within : slot< d*d+2*d) :
    rawField d u.val v.val slot<(fields B).length := by
  rw [fields_length]
  unfold rawField
  split_ifs with first second
  · omega
  · have hu := Nat.mul_le_mul_right d (Nat.succ_le_of_lt u.isLt)
    have off : slot-d*d< d := by omega
    nlinarith only [hu,off]
  · have hv := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    have off : slot-(d*d+d)< d := by omega
    nlinarith only [hv,off]

theorem rawInputs_basis (B : BasisData n d) (u v : Fin n) (i j : Fin d) :
    rawInputs B u v (Circuit.rawBasisIndex d i j)=B.basis i j := by
  have within : i.val*d+j.val< d*d := by
    have mul := Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
    have hj := j.isLt
    nlinarith only [mul,hj]
  simpa [rawInputs,rawField,Circuit.rawBasisIndex,within,fields_basis_get] using
    congrArg (fun x : Option ℤ => x.getD 0) (fields_basis_get B i j)

theorem rawInputs_first (B : BasisData n d) (u v : Fin n) (i : Fin d) :
    rawInputs B u v (Circuit.firstOriginIndex d i)=B.origin u i := by
  have first : ¬d*d+i.val< d*d := by omega
  have second : d*d+i.val< d*d+d := by have := i.isLt; omega
  simpa [rawInputs,rawField,Circuit.firstOriginIndex,first,second] using
    congrArg (fun x : Option ℤ => x.getD 0) (fields_origin_get B u i)

theorem rawInputs_second (B : BasisData n d) (u v : Fin n) (i : Fin d) :
    rawInputs B u v (Circuit.secondOriginIndex d i)=B.origin v i := by
  have first : ¬d*d+d+i.val< d*d := by omega
  have second : ¬d*d+d+i.val< d*d+d := by omega
  simpa [rawInputs,rawField,Circuit.secondOriginIndex,first,second] using
    congrArg (fun x : Option ℤ => x.getD 0) (fields_origin_get B v i)

def sourceRank (d u v : ℕ) : Fin 3 → ℕ | 0 => 0 | 1 => d*d+u*d | _ => d*d+v*d

def sourceLayout (B : BasisData n d) (u v : Fin n) (base : ℕ) : SourceLoad.Layout where
  dimension := d
  length := precision B
  base := base
  source := fun block => 4+sourceRank d u.val v.val block*precision B

theorem rawField_block (u v : Fin n) (block : Fin 3) (slot : ℕ) (within : slot< SourceLoad.count d block) :
    rawField d u.val v.val (SourceLoad.start d block+slot)=sourceRank d u.val v.val block+slot := by
  fin_cases block
  · change slot< d*d at within
    simp [SourceLoad.start,rawField,within,sourceRank]
  · change slot< d at within
    have first : ¬d*d+slot< d*d := by omega
    have second : d*d+slot< d*d+d := by omega
    norm_num [SourceLoad.start,rawField,sourceRank,first,second]
  · change slot< d at within
    have first : ¬d*d+d+slot< d*d := by omega
    have second : ¬d*d+d+slot< d*d+d := by omega
    norm_num [SourceLoad.start,rawField,sourceRank,first,second]

theorem sourceRank_within (B : BasisData n d) (u v : Fin n) (block : Fin 3) (slot : ℕ)
    (within : slot< SourceLoad.count d block) :
    sourceRank d u.val v.val block+slot<(fields B).length := by
  rw [←rawField_block u v block slot within]
  exact rawField_within B u v _ (SourceLoad.slot_within d block slot within)

theorem sourceLayout_bits (B : BasisData n d) (u v : Fin n) (base : ℕ) (block : Fin 3)
    (slot : ℕ) (within : slot< SourceLoad.count d block) (i : ℕ) (digit : i< precision B) :
    inputMemory B ((sourceLayout B u v base).source block+slot*precision B+i)≤1 := by
  have bit := inputMemory_field_bits B (sourceRank d u.val v.val block+slot)
    (sourceRank_within B u v block slot within) i digit
  convert bit using 1 <;> dsimp [sourceLayout] <;> congr 1 <;> ring

theorem sourceLayout_encoding (B : BasisData n d) (u v : Fin n) (base : ℕ) (block : Fin 3)
    (slot : ℕ) (within : slot< SourceLoad.count d block) :
    (value (inputMemory B) ((sourceLayout B u v base).source block+slot*precision B) (precision B) : ℤ)=
      rawInputs B u v (SourceLoad.inputIndex d block slot within)%(2^precision B : ℕ) := by
  have inside := sourceRank_within B u v block slot within
  have encoded := inputMemory_field_value B (sourceRank d u.val v.val block+slot) inside
  have index : rawInputs B u v (SourceLoad.inputIndex d block slot within)=
      (fields B)[sourceRank d u.val v.val block+slot] := by
    simp only [rawInputs,SourceLoad.inputIndex,rawField_block u v block slot within,List.getElem?_eq_getElem inside,Option.getD_some]
  rw [index]
  convert encoded using 1 <;> dsimp [sourceLayout] <;> congr 2 <;> push_cast <;> ring

theorem original_source_before (B : BasisData n d) (u v : Fin n) (base : ℕ) (block : Fin 3)
    (slot : ℕ) (within : slot< SourceLoad.count d block) (i : ℕ) (digit : i< precision B) :
    (sourceLayout B u v base).source block+slot*precision B+i<(words B).length+1 := by
  have rank := sourceRank_within B u v block slot within
  rw [fields_length] at rank
  have mul := Nat.mul_le_mul_right (precision B) (Nat.succ_le_of_lt rank)
  rw [words_length]
  dsimp only [sourceLayout]
  nlinarith only [mul,digit]

theorem rawNumerator_eval (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d) :
    (Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)=
      B.basis.adjugate.mulVec (fun j => B.origin u j-B.origin v j+(if j=direction then 1 else 0)) coordinate :=
  Circuit.rawNumeratorCircuit_eval (rawInputs B u v) B.basis (B.origin u) (B.origin v) direction coordinate
    (rawInputs_basis B u v) (rawInputs_first B u v) (rawInputs_second B u v)

end LeanTrominoes.Domino.WordRAM

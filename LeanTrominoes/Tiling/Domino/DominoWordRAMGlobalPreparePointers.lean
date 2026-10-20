/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareReserve

/-! # Checked pointers into the single shared global block -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

def pointerMoves (d : Nat) : List (Fin 128 × Nat) :=
  [(H.zero,0),(H.determinant,1),(H.twice,2),(H.parities,3),(low SourceBlocks.circuitBase,3+d)]

def pointersCode : List (Fin 128 × Nat) → Code
  | [] => .atom (.copy H.precision H.precision)
  | p::rest => .seq (HeaderPointer.program p.1 p.2) (pointersCode rest)

def pointersState (moves : List (Fin 128 × Nat)) (data : Data) :=
  moves.foldl (fun before p => HeaderPointer.state before p.1 p.2) data

theorem pointers_exec {w base length : Nat} (moves : List (Fin 128 × Nat)) (data : Data)
    (baseEq : data.1 Reserve.base=base) (lengthEq : data.1 Reserve.precision=length)
    (lengthFits : Fits w length)
    (safe : ∀ p∈moves, p.1≠Reserve.precision ∧ p.1≠Reserve.base)
    (slots : ∀ p∈moves, Fits w p.2) (products : ∀ p∈moves, Fits w (p.2*length : Nat))
    (addresses : ∀ p∈moves, Fits w (base+p.2*length : Nat)) :
    NaturalData.Exec w (pointersCode moves) data (pointersState moves data) (3*moves.length+1) := by
  induction moves generalizing data with
  | nil =>
    simpa [pointersCode,pointersState,NaturalData.set] using NaturalData.copy_exec data H.precision H.precision (lengthEq ▸ lengthFits)
  | cons p rest ih =>
    have first := HeaderPointer.program_exec data p.1 p.2 (safe p List.mem_cons_self).1 (safe p List.mem_cons_self).2
      (slots p List.mem_cons_self) (by simpa only [lengthEq] using products p List.mem_cons_self)
      (by simpa only [baseEq,lengthEq] using addresses p List.mem_cons_self)
    have later := ih (HeaderPointer.state data p.1 p.2)
      ((HeaderPointer.state_other data p.1 p.2 Reserve.base (Ne.symm (safe p List.mem_cons_self).2) (by decide)).trans baseEq)
      ((HeaderPointer.state_other data p.1 p.2 Reserve.precision (Ne.symm (safe p List.mem_cons_self).1) (by decide)).trans lengthEq)
      (fun q hq => safe q (List.mem_cons_of_mem _ hq)) (fun q hq => slots q (List.mem_cons_of_mem _ hq))
      (fun q hq => products q (List.mem_cons_of_mem _ hq)) (fun q hq => addresses q (List.mem_cons_of_mem _ hq))
    have trace := first.seq later
    have cost : 3+(3*rest.length+1)=3*(p::rest).length+1 := by simp only [List.length_cons]; omega
    rw [cost] at trace
    exact trace

theorem pointersState_memory (moves : List (Fin 128 × Nat)) (data : Data) : (pointersState moves data).2=data.2 := by
  induction moves generalizing data with
  | nil => rfl
  | cons p rest ih => exact (ih (HeaderPointer.state data p.1 p.2)).trans rfl

theorem pointersState_fixed (moves : List (Fin 128 × Nat)) (data : Data) (reg : Fin 128)
    (scratch : reg≠Reserve.factorRegister) (safe : ∀ p∈moves, reg≠p.1) :
    (pointersState moves data).1 reg=data.1 reg := by
  induction moves generalizing data with
  | nil => rfl
  | cons p rest ih =>
    exact (ih (HeaderPointer.state data p.1 p.2) (fun q hq => safe q (List.mem_cons_of_mem _ hq))).trans
      (HeaderPointer.state_other data p.1 p.2 reg (safe p List.mem_cons_self) scratch)

theorem global_pointers_exec {n d w : Nat} (B : BasisData n d) (data : Data)
    (base : data.1 Reserve.base=inputEnd B) (length : data.1 Reserve.precision=WordRAM.precision B)
    (width : Fits w (resourceBound B)) :
    NaturalData.Exec w (pointersCode (pointerMoves d)) data (pointersState (pointerMoves d) data) 16 := by
  have within : ∀ p∈pointerMoves d, p.2≤factor d := by
    intro p hp
    simp only [pointerMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> unfold factor <;> omega
  apply pointers_exec (base:=inputEnd B) (length:=WordRAM.precision B) _ _ base length
    (Allocation.nat_fits_le width (resource_precision B))
  · simp [pointerMoves,H.zero,H.determinant,H.twice,H.parities,low,SourceBlocks.circuitBase,Reserve.precision,Reserve.base]
  · intro p hp
    apply Allocation.nat_fits_le width
    have bound := within p hp
    unfold resourceBound
    omega
  · intro p hp
    apply Allocation.nat_fits_le width
    have bound := Nat.mul_le_mul_right (WordRAM.precision B) (within p hp)
    unfold resourceBound
    omega
  · intro p hp
    apply Allocation.nat_fits_le width
    have bound := Nat.mul_le_mul_right (WordRAM.precision B) (within p hp)
    have endBound := resource_end B
    unfold endAddress at endBound
    omega

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128

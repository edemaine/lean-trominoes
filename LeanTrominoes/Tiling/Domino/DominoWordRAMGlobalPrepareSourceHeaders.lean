/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPreparePointers

/-! # Installing the source loader's private pointer arguments -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

def sourceMoves : List (Fin 128 × Fin 128) :=
  [(low SourceBlocks.firstOrigin,OriginPointers128.H.first),(low SourceBlocks.secondOrigin,OriginPointers128.H.second),
    (low SourceBlocks.precision,H.precision)]
def sourceSetup : Code := .seq (Assignments.code (low SourceBlocks.precision) H.precision sourceMoves)
  (.atom (.constant (low SourceBlocks.basisBase) 4))
def sourcePrepared (data : Data) :=
  (Assignments.state (low SourceBlocks.precision) H.precision sourceMoves data).set (low SourceBlocks.basisBase) 4

attribute [local simp] low SourceBlocks.firstOrigin SourceBlocks.secondOrigin SourceBlocks.precision SourceBlocks.circuitBase SourceBlocks.basisBase
  OriginPointers128.H.first OriginPointers128.H.second H.precision H.n H.zero H.determinant H.twice H.parities H.frontier
  Reserve.base Reserve.precision Reserve.frontier Reserve.factorRegister NaturalData.set

theorem sourceSetup_exec {w : Nat} (data : Data)
    (lengthFits : Fits w (data.1 H.precision)) (firstFits : Fits w (data.1 OriginPointers128.H.first))
    (secondFits : Fits w (data.1 OriginPointers128.H.second)) (four : Fits w (4 : Nat)) :
    NaturalData.Exec w sourceSetup data (sourcePrepared data) 5 := by
  have copies : NaturalData.Exec w (Assignments.code (low SourceBlocks.precision) H.precision sourceMoves)
      data (Assignments.state (low SourceBlocks.precision) H.precision sourceMoves data) 4 := by
    apply Assignments.exec data (low SourceBlocks.precision) H.precision sourceMoves lengthFits
    · intro p hp
      simp only [sourceMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact firstFits
      · exact secondFits
      · exact lengthFits
    · simp [sourceMoves]
    · simp [sourceMoves]
  exact copies.seq (NaturalData.constant_exec _ (low SourceBlocks.basisBase) 4 four)

theorem sourcePrepared_high (data : Data) (reg : Fin 128) (high : 64≤reg.val) :
    (sourcePrepared data).1 reg=data.1 reg := by
  have ne (dst : Fin 128) (small : dst.val<64) : reg≠dst := by intro equal; have := congrArg Fin.val equal; omega
  simp only [sourcePrepared,Assignments.state,sourceMoves,List.foldl_cons,List.foldl_nil,NaturalData.set,
    Function.update_of_ne (ne (low SourceBlocks.basisBase) (by decide)),
    Function.update_of_ne (ne (low SourceBlocks.precision) (by decide)),
    Function.update_of_ne (ne (low SourceBlocks.firstOrigin) (by decide)),
    Function.update_of_ne (ne (low SourceBlocks.secondOrigin) (by decide))]

theorem sourcePrepared_values (data : Data) :
    (sourcePrepared data).1 (low SourceBlocks.firstOrigin)=data.1 OriginPointers128.H.first ∧
    (sourcePrepared data).1 (low SourceBlocks.secondOrigin)=data.1 OriginPointers128.H.second ∧
    (sourcePrepared data).1 (low SourceBlocks.precision)=data.1 H.precision ∧
    (sourcePrepared data).1 (low SourceBlocks.circuitBase)=data.1 (low SourceBlocks.circuitBase) ∧
    (sourcePrepared data).1 (low SourceBlocks.basisBase)=4 := by
  simp [sourcePrepared,Assignments.state,sourceMoves]

theorem pointed_values (data : Data) (d : Nat) :
    (pointersState (pointerMoves d) data).1 H.zero=data.1 Reserve.base ∧
    (pointersState (pointerMoves d) data).1 H.determinant=data.1 Reserve.base+data.1 Reserve.precision ∧
    (pointersState (pointerMoves d) data).1 H.twice=data.1 Reserve.base+2*data.1 Reserve.precision ∧
    (pointersState (pointerMoves d) data).1 H.parities=data.1 Reserve.base+3*data.1 Reserve.precision ∧
    (pointersState (pointerMoves d) data).1 (low SourceBlocks.circuitBase)=data.1 Reserve.base+(3+d)*data.1 Reserve.precision := by
  simp [pointersState,pointerMoves,HeaderPointer.state,Nat.add_comm,Nat.add_assoc]

theorem pointed_fixed (data : Data) (d : Nat) (reg : Fin 128)
    (safe : reg≠H.zero ∧ reg≠H.determinant ∧ reg≠H.twice ∧ reg≠H.parities ∧
      reg≠low SourceBlocks.circuitBase ∧ reg≠Reserve.factorRegister) :
    (pointersState (pointerMoves d) data).1 reg=data.1 reg := by
  apply pointersState_fixed _ _ _ safe.2.2.2.2.2
  intro p hp
  simp only [pointerMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact safe.1
  · exact safe.2.1
  · exact safe.2.2.1
  · exact safe.2.2.2.1
  · exact safe.2.2.2.2.1

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128

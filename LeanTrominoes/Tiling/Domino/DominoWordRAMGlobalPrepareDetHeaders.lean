/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareLoad

/-! # Restoring determinant arguments after the original-input copy -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

def determinantMoves : List (Fin 128 × Fin 128) :=
  [(low DeterminantSetup.G.precision,H.precision),(low DeterminantSetup.G.zero,H.zero),
    (low DeterminantSetup.G.absolute,H.determinant),(low DeterminantSetup.G.twice,H.twice)]
def determinantHeaders (d : Nat) : Code := .seq
  (HeaderPointer.program (low DeterminantSetup.G.circuit) (3+d))
  (Assignments.code (low DeterminantSetup.G.precision) H.precision determinantMoves)
def determinantPrepared (d : Nat) (data : Data) :=
  Assignments.state (low DeterminantSetup.G.precision) H.precision determinantMoves
    (HeaderPointer.state data (low DeterminantSetup.G.circuit) (3+d))

attribute [local simp] H.precision H.zero H.determinant H.twice Reserve.base Reserve.precision Reserve.factorRegister
  low DeterminantSetup.G.precision DeterminantSetup.G.circuit DeterminantSetup.G.zero DeterminantSetup.G.absolute
  DeterminantSetup.G.twice NaturalData.set

theorem determinant_widths {n d w : Nat} (B : BasisData n d) (width : Fits w (resourceBound B)) :
    DeterminantSetup.Widths (geometry B) w := by
  constructor
  · exact Allocation.nat_fits_le width (by have := resource_small B; omega)
  · exact Allocation.nat_fits_le width (resource_precision B)
  · apply Allocation.nat_fits_le width
    change Circuit.resourceBound (circuitBase B) (WordRAM.precision B) (DeterminantSetup.slots d)≤resourceBound B
    unfold resourceBound; omega
  all_goals
    apply Allocation.nat_fits_le width
    change _≤resourceBound B
    have endBound := resource_end B
    have grow := Nat.mul_le_mul_right (WordRAM.precision B) (show 3≤factor d by unfold factor; omega)
    dsimp only [geometry]
    unfold endAddress at endBound
    omega

theorem determinantHeaders_exec {n d w : Nat} (B : BasisData n d) (data : Data)
    (base : data.1 Reserve.base=inputEnd B) (precision : data.1 H.precision=WordRAM.precision B)
    (zero : data.1 H.zero=inputEnd B) (det : data.1 H.determinant=inputEnd B+WordRAM.precision B)
    (twice : data.1 H.twice=inputEnd B+2*WordRAM.precision B) (width : Fits w (resourceBound B)) :
    NaturalData.Exec w (determinantHeaders d) data (determinantPrepared d data) 8 ∧
      DeterminantSetup.Controls (geometry B) (Lower (determinantPrepared d data)) ∧
      (determinantPrepared d data).2=data.2 ∧
      (∀ reg : Fin 128, 64≤reg.val → (determinantPrepared d data).1 reg=data.1 reg) := by
  have within : 3+d≤factor d := by unfold factor; omega
  have product := Nat.mul_le_mul_right (WordRAM.precision B) within
  have three := Nat.mul_le_mul_right (WordRAM.precision B) (show 3≤factor d by unfold factor; omega)
  have ending := resource_end B
  unfold endAddress at ending
  have pointer := HeaderPointer.program_exec data (low DeterminantSetup.G.circuit) (3+d) (by decide) (by decide)
    (Allocation.nat_fits_le width (by unfold resourceBound; unfold factor at within; omega))
    (by rw [precision]; exact Allocation.nat_fits_le width (by unfold resourceBound; omega))
    (by rw [base,precision]; exact Allocation.nat_fits_le width (by omega))
  let pointed := HeaderPointer.state data (low DeterminantSetup.G.circuit) (3+d)
  have fixed (reg : Fin 128) (different : reg≠low DeterminantSetup.G.circuit ∧ reg≠Reserve.factorRegister) :
      pointed.1 reg=data.1 reg := HeaderPointer.state_other data _ _ reg different.1 different.2
  have copy : NaturalData.Exec w
      (Assignments.code (low DeterminantSetup.G.precision) H.precision determinantMoves) pointed
      (determinantPrepared d data) 5 := by
    apply Assignments.exec pointed (low DeterminantSetup.G.precision) H.precision determinantMoves
      (by rw [fixed _ (by decide),precision]; exact Allocation.nat_fits_le width (resource_precision B))
    · intro p hp
      simp only [determinantMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      all_goals rw [fixed _ (by decide)]
      · rw [precision]; exact Allocation.nat_fits_le width (resource_precision B)
      · rw [zero]; exact Allocation.nat_fits_le width (resource_input B)
      · rw [det]; exact Allocation.nat_fits_le width (by omega)
      · rw [twice]; exact Allocation.nat_fits_le width (by omega)
    · simp [determinantMoves]
    · simp [determinantMoves]
  refine ⟨pointer.seq copy,?_,rfl,?_⟩
  · constructor
    all_goals simp [determinantPrepared,Assignments.state,determinantMoves,HeaderPointer.state,
      NaturalData.lower,geometry,precision,zero,det,twice,base,circuitBase,Nat.add_comm,Nat.add_assoc]
  · intro reg high
    have ne (dst : Fin 128) (small : dst.val<64) : reg≠dst := by intro same; have := congrArg Fin.val same; omega
    simp only [determinantPrepared,Assignments.state,determinantMoves,List.foldl_cons,List.foldl_nil,NaturalData.set,
      Function.update_of_ne (ne (low DeterminantSetup.G.precision) (by decide)),
      Function.update_of_ne (ne (low DeterminantSetup.G.zero) (by decide)),
      Function.update_of_ne (ne (low DeterminantSetup.G.absolute) (by decide)),
      Function.update_of_ne (ne (low DeterminantSetup.G.twice) (by decide))]
    exact fixed reg ⟨ne _ (by decide),ne _ (by decide)⟩

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
